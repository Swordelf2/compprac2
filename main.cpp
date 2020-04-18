#include <iostream>

#ifdef __cplusplus
#define export exports
extern "C" {
#include <qbe/all.h>
}
#undef export
#else
#include <qbe/all.h>
#endif

#include <stdio.h>
#include <string.h>

#include <algorithm>
#include <cstdlib>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <utility>

const uint END_BLOCK_ID = (1u << 31u) - 1;

struct BlkInfo {
    Blk *blk;
    // If this block has already been visited during postorder traversal
    bool visited;
    // Reverse graph rpo id
    int rid;
    // immediate postdominator
    int rdom;
    // Postdominance frontier
    std::unordered_set<uint> rfron;
    // Whether this block is useful (contains at least 1 useful instruction)
    bool useful;
};

// Auxillary function for combining hashes of two objects into one
template <class T>
inline static void hash_combine(std::size_t& s, const T& v) {
    std::hash<T> h;
    s ^= h(v) + 0x9e3779b9 + (s << 6) + (s >> 2);
}


// Hash function for `Use`
struct UseHash {
    std::size_t operator()(const Use& use) const {
        size_t result = 0;
        hash_combine(result, use.bid);
        if (use.type == Use::UPhi) {
            hash_combine(result, reinterpret_cast<size_t>(use.u.phi));
        } else if (use.type == Use::UIns) {
            hash_combine(result, reinterpret_cast<size_t>(use.u.ins));
        }
        return result;
    }
};

bool operator==(const Use &use1, const Use &use2) {
    return use1.bid == use2.bid &&
        use1.type == use2.type &&
        ((use1.type == Use::UPhi && use1.u.phi == use2.u.phi) ||
         (use1.type == Use::UIns && use1.u.ins == use2.u.ins) ||
         use1.type == Use::UJmp);
}

// Mapping from block_id to its BlkInfo struct
std::unordered_map<uint, BlkInfo> id2blkinfo;
std::vector<uint> rrpo;
std::unordered_set<Use, UseHash> use_marks;
// Mapping from a variable to its def (ssa => single def)
std::unordered_map<uint, Use> tmp_def;
std::vector<Use> work_list;

// Cast phi to Use
Use to_use(uint bid, Phi *phi) {
    return Use {
        Use::UPhi,
        static_cast<int>(bid),
        { .phi = phi }
    };
}

// Cast Ins to Use
Use to_use(uint bid, Ins *ins) {
    return Use {
        Use::UIns,
        static_cast<int>(bid),
        { .ins = ins }
    };
}

// Cast jump to Use
Use to_use(uint bid) {
    return Use {
        Use::UJmp,
        static_cast<int>(bid),
        nullptr
    };
}

// Mark a use during the Mark phase of the main algorithm
void mark_use(const Use &use) {
    if (use_marks.insert(use).second) {
        work_list.push_back(use);
        // Mark the block as useful
        id2blkinfo[use.bid].useful = true;
    }
}

// Retrieve block name by id
const char *id2name(uint id) {
    const BlkInfo &blk_info = id2blkinfo[id];
    return blk_info.blk ? blk_info.blk->name : "end_block";
}

/*
// Used to remove unreachable blocks
void preorder_traverse(Blk *blk) {
    id2blkinfo[blk->id].visited = true;
    if (blk->s1 && !id2blkinfo[blk->s1->id].visited) {
        preorder_traverse(blk->s1);
    }
    if (blk->s2 && !id2blkinfo[blk->s2->id].visited) {
        preorder_traverse(blk->s2);
    }
}
*/

// Postorder traversal of an implicitly reversed cfg
void postorder_traverse(Blk *blk) {
    for (uint pred_num = 0; pred_num < blk->npred; ++pred_num) {
        Blk *pred = blk->pred[pred_num];
        if (id2blkinfo[pred->id].visited == false) {
            id2blkinfo[pred->id].visited = true;
            postorder_traverse(pred);
        }
    }
    // Visit this block
    rrpo.push_back(blk->id);
}

void build_rrpo(Fn *fn) {
    // Find all end blocks
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        if (isret(blk->jmp.type)) {
            // Mark it as visited
            id2blkinfo[blk->id].visited = true;
            postorder_traverse(blk);
            // Immedately set its imm postdom to the imaginary end block
            id2blkinfo[blk->id].rdom = END_BLOCK_ID;
        }
    }
    // Finalize creation of rrpo by adding the imaginary end block and reversing it
    rrpo.push_back(END_BLOCK_ID);
    std::reverse(rrpo.begin(), rrpo.end());
    // Assign the rrpo indices in the BlkInfo structs
    for (uint i = 0; i < rrpo.size(); ++i) {
        id2blkinfo[rrpo[i]].rid = i;
    }
}

uint rdom_intersect(uint b1, uint b2) {
    uint finger1 = id2blkinfo[b1].rid;
    uint finger2 = id2blkinfo[b2].rid;
    while (finger1 != finger2) {
        while (finger1 > finger2) {
            finger1 = id2blkinfo[id2blkinfo[rrpo[finger1]].rdom].rid;
        }
        while (finger2 > finger1) {
            finger2 = id2blkinfo[id2blkinfo[rrpo[finger2]].rdom].rid;
        }
    }
    return rrpo[finger1];
}

// A simple. fast dominance algorithm ... 
void build_rdom() {
    // Set the imaginary end block's postdom equal to itself
    id2blkinfo[rrpo[0]].rdom = rrpo[0];
    // Loop until nothing changes
    bool changed = true;
    while (changed) {
        changed = false;
        // Iterate over all blocks
        for (uint i = 1; i < rrpo.size(); ++i) {
            uint id = rrpo[i];
            BlkInfo &blk_info = id2blkinfo[id];
            bool s1p = false, s2p = false;
            if (blk_info.blk->s1) {
                s1p = id2blkinfo[blk_info.blk->s1->id].rdom != -1; // whether s1 is processed
            }
            if (blk_info.blk->s2) {
                s2p = id2blkinfo[blk_info.blk->s2->id].rdom != -1; // whether s2 is processed
            }
            // Compute new_rdom as the intersection of all processed predecessors
            // (successors in the reverse graph)
            int new_rdom;
            if (s1p && s2p) {
                new_rdom = rdom_intersect(blk_info.blk->s1->id, blk_info.blk->s2->id);
            } else if (s1p && !s2p) {
                new_rdom = blk_info.blk->s1->id;
            } else if (!s1p && s2p) {
                new_rdom = blk_info.blk->s2->id;
            } else {
                // This is an end block, skip it
                continue;
            }
            // Update the rdom
            if (new_rdom != blk_info.rdom) {
                blk_info.rdom = new_rdom;
                changed = true;
            }
        }
    }
}

void rfron_runup(uint b, uint p) {
    uint runner = p;
    uint b_rdom = id2blkinfo[b].rdom;
    while (runner != b_rdom) {
        id2blkinfo[runner].rfron.insert(b);
        runner = id2blkinfo[runner].rdom;
    }
}

void build_rfron() {
    // Skip the imaginary end block
    for (uint i = 1; i < rrpo.size(); ++i) {
        uint id = rrpo[i];
        const BlkInfo &blk_info = id2blkinfo[id];
        if (blk_info.blk->s1 && blk_info.blk->s2) {
            rfron_runup(id, blk_info.blk->s1->id);
            rfron_runup(id, blk_info.blk->s2->id);
        }
    }
}

static void readfn (Fn *fn) {
    fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
    fillpreds(fn);
    filluse(fn);
    ssa(fn);

    // Construct initial BlkInfo for each block
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        // Construct the BlkInfo for this block
        BlkInfo blk_info = BlkInfo { blk, false, -1, -1, std::unordered_set<uint>(), false};
        // Insert it into the map
        id2blkinfo.insert(std::make_pair(blk->id, blk_info));
    }

    // Create an imaginary `end` block
    id2blkinfo[END_BLOCK_ID] = BlkInfo { nullptr, false, -1, END_BLOCK_ID, 
            std::unordered_set<uint>(), false };
    build_rrpo(fn);
    build_rdom();
    build_rfron();
    /* Debug output
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        std::cout << blk->name << ' ' << id2blkinfo[blk->id].rid << std::endl;
        std::cout << "Imm dominator: " << id2blkinfo[id2blkinfo[blk->id].rdom].blk->name << std::endl;
        std::cout << "Dom Frontier: ";
        for (uint id : id2blkinfo[blk->id].rfron) {
            std::cout << id2blkinfo[id].blk->name << ' ';
        }
        std::cout << std::endl;
    }
    */

    /* Mark */
    // First mark all the critical instructions and push them into the worklist
    // Also fill the `tmp_def` map
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        // Phi functions
        for (Phi *phi = blk->phi; phi; phi = phi->link) {
            if (phi->to.type == RTmp) {
                if (!tmp_def.insert(std::make_pair<uint, Use>(
                            static_cast<uint>(phi->to.val),
                            to_use(blk->id, phi))).second) {
                    std::cerr << "Var defined twice in phi" << std::endl;
                    abort();
                }
            }
        }
        // Instructions
        for (Ins *ins = blk->ins; ins < blk->ins + blk->nins; ++ins) {
            Use use = to_use(blk->id, ins);
            // Store into memory instruction, or an argument to a function call,
            // or a function call itself, all are critical
            if (isstore(ins->op) || ins->op == Oarg || ins->op == Ocall || ins->op == Ovacall) {
                mark_use(use);
            } else if (ins->to.type == RTmp && ins->to.val != 0) {
                // TODO: maybe don't need this != 0
                // Otherwise just store the definition of a variable
                if (!tmp_def.insert(std::make_pair(
                            static_cast<uint>(ins->to.val),
                            use)).second) {
                    std::cerr << "Var defined twice in ins" << std::endl;
                    std::abort();
                }
            }
        }
        // Jump
        if (isret(blk->jmp.type)) {
            mark_use(to_use(blk->id));
        }
    }

    // Main iteration over the worklist
    while (!work_list.empty()) {
        Use use = work_list.back();
        work_list.pop_back();

        const BlkInfo &blk_info = id2blkinfo[use.bid];
        // Mark oll definitions of all arguments of this Use
        switch (use.type) {
            case Use::UPhi: {
                Phi *phi = use.u.phi;
                for (Ref *arg = phi->arg; arg < phi->arg + phi->narg; ++arg) {
                    if (arg->type == RTmp) {
                        mark_use(tmp_def[arg->val]);
                    }
                }
                break;
            }
            case Use::UIns: {
                Ins *ins = use.u.ins;
                for (uint i = 0; i < 2; ++i) {
                    Ref arg = ins->arg[i];
                    // TODO: maybe arg.val != 0 not needed here
                    if (arg.type == RTmp && arg.val != 0) {
                        mark_use(tmp_def[arg.val]);
                    }
                }
                break;
            }
            case Use::UJmp: {
                Ref arg = id2blkinfo[use.bid].blk->jmp.arg;
                if (arg.type == RTmp) {
                    mark_use(tmp_def[arg.val]);
                }
                break;
            }
            default:
                ;
        }

        // Now mark all jumps of all blocks in RDF of this block
        for (uint blk_id : blk_info.rfron) {
            mark_use(to_use(blk_id));
        }
    }

    /* Debug output */
    for (uint id: rrpo) {
        const BlkInfo &blk_info = id2blkinfo[id];
        std::cout << "Block: " << id2name(id) << "  " << "id: " << id << std::endl;
        std::cout << "rdom: " << id2name(blk_info.rdom) << std::endl;
        std::cout << "rfron: ";
        for (uint fron_elem : blk_info.rfron) {
            std::cout << id2name(fron_elem) << ' ';
        }
        std::cout << "useful: " << blk_info.useful << std::endl;
        std::cout << std::endl << std::endl;
    }

    /* Sweep */
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        // Phi functions
        Phi *prev = nullptr;
        // TODO: maybe free(phi)
        for (Phi *phi = blk->phi; phi; phi = phi->link) {
            // If not marked
            if (use_marks.find(to_use(blk->id, phi)) == use_marks.end()) {
                // Remove this node from the list
                if (prev) {
                    prev->link = phi->link;
                } else {
                    blk->phi = phi;
                }
            } else {
                prev = phi;
            }
        }

        // Instructions
        for (Ins *ins = blk->ins; ins < blk->ins + blk->nins; ++ins) {
            // If not marked
            if (use_marks.find(to_use(blk->id, ins)) == use_marks.end()) {
                ins->op = Onop;
                ins->to = R;
                ins->arg[0] = R;
                ins->arg[1] = R;
            }
        }

        // Jumps
        // If not marked
        if (use_marks.find(to_use(blk->id)) == use_marks.end()) {
            // Find the closest useful postdominator
            uint post_dom = id2blkinfo[blk->id].rdom;
            while (!id2blkinfo[post_dom].useful) {
                post_dom = id2blkinfo[post_dom].rdom;
            }

            // Reset branches, only one leading to this block's closest useful postdominator
            blk->s1 = id2blkinfo[post_dom].blk;
            blk->s2 = nullptr;
            blk->jmp.arg = R;
            blk->jmp.type = Jjmp;
        }
    }
    
    /*
    // Remove all useless blocks
    Blk *prev = nullptr;
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        // If useless
        if (!id2blkinfo[blk->id].useful) {
            // Remove this block
            if (prev) {
                prev->link = blk->link;
            } else {
                fn->start = blk;
            }
        } else {
            prev = blk;
        }
    }
    */

            

    /* Debug output
    for (int t = Tmp0; t < fn->ntmp; ++t) {
        const Tmp &tmp = fn->tmp[t];
        std::cout << fn->tmp[t].name << std::endl;
        std::cout << "Uses: " << std::endl;
        for (unsigned use_num = 0; use_num < tmp.nuse; ++use_num) {
            const Use &use = tmp.use[use_num];
            Blk *use_blk = id2blkinfo[use.bid].blk;
            std::cout << use_blk->name << ' ';
            if (use.type == Use::UIns) {
                std::cout << "Instruction";
            } else if (use.type == Use::UJmp) {
                std::cout << "Jump";
            } else if (use.type == Use::UPhi) {
                std::cout << "Phi function";
            }
            std::cout << std::endl;
        }
    }
    std::cout << std::endl << std::endl;
    */

    /*
    // Remove all unreachable blocks myself
    // Visit all reachable
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        id2blkinfo[blk->id].visited = false;
    }
    preorder_traverse(fn->start);

    // Remove not visited
    Blk *prev = nullptr;
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        // If not visited
        if (!id2blkinfo[blk->id].visited) {
            // Remove this block
            if (prev) {
                prev->link = blk->link;
            } else {
                fn->start = blk;
            }
        } else {
            prev = blk;
        }
    }
    */

    fillpreds(fn); // Either call this, or keep track of preds manually when rewriting branches.
    fillrpo(fn); // As a side effect, fillrpo removes any unreachable blocks.
    printfn(fn, stdout);
}

static void readdat (Dat *dat) {
    (void) dat;
}

int main () {
    char STDIN_NAME[] = "<stdin>";
    parse(stdin, STDIN_NAME, readdat, readfn);
    freeall();
}
