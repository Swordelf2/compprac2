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
};

// Mapping from block_id to its BlkInfo struct
std::unordered_map<uint, BlkInfo> id2blkinfo;

std::vector<uint> rrpo;

Blk *end_blk = nullptr;

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
    // Find the end block
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        if (isret(blk->jmp.type)) {
            end_blk = blk;
            break;
        }
    }
    if (!end_blk) {
        std::cerr << "Could not find end block" << std::endl;
        std::abort();
    }
    // Mark it as visited
    id2blkinfo[end_blk->id].visited = true;
    postorder_traverse(end_blk);
    // Finalize creation of rrpo by reversing it
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
    for (uint id: rrpo) {
        id2blkinfo[id].rdom = -1;
    }
    id2blkinfo[end_blk->id].rdom = end_blk->id;
    // Loop until nothing changes
    bool changed = true;
    while (changed) {
        changed = false;
        // Iterate over all except end_blk
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
                std::cerr << "Both blocks unprocessed" << std::endl;
                std::abort();
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
    for (uint id: rrpo) {
        const BlkInfo &blk_info = id2blkinfo[id];
        if (blk_info.blk->s1 && blk_info.blk->s2) {
            rfron_runup(id, blk_info.blk->s1->id);
            rfron_runup(id, blk_info.blk->s2->id);
        }
    }
}

static int useful(Ins* i) {
    return 1;
}

static void readfn (Fn *fn) {
    fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
    fillpreds(fn);
    ssa(fn);
    filluse(fn);

    // Construct initial BlkInfo for each block
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        // Construct the BlkInfo for this block
        BlkInfo blk_info = BlkInfo { blk, false, -1 };
        // Insert it into the map
        id2blkinfo.insert(std::make_pair(blk->id, blk_info));
    }

    build_rrpo(fn);
    build_rdom();
    build_rfron();
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        std::cout << blk->name << ' ' << id2blkinfo[blk->id].rid << std::endl;
        std::cout << "Imm dominator: " << id2blkinfo[id2blkinfo[blk->id].rdom].blk->name << std::endl;
        std::cout << "Dom Frontier: ";
        for (uint id : id2blkinfo[blk->id].rfron) {
            std::cout << id2blkinfo[id].blk->name << ' ';
        }
        std::cout << std::endl;
    }

    //..
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        for (Ins *i = blk->ins; i < &blk->ins[blk->nins]; ++i) {
            if (!useful(i)) {
                i->op = Onop;
                i->to = R;
                i->arg[0] = R;
                i->arg[1] = R;
            }
        }

        // ... (work with jmp)
    }

    /*
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

    fillpreds(fn); // Either call this, or keep track of preds manually when rewriting branches.
    fillrpo(fn); // As a side effect, fillrpo removes any unreachable blocks.
    printfn(fn, stdout);
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}
