#include <cstdio>
#include <cstring>
#include <cmath>
#include <utility>
#include <vector>
#include <set>

using namespace std;
const int MAXEDGE = 260000;
const int MAXVERTEX =  800;
int edge_num;
int node_num;
//int in_L[MAXEDGE];
int tabuAdd, tabuRemove;
int delta = 3;
int maxSteps = 1000;
//int in_L_num;
//set<int> UL;
struct node {
    vector<int> edge;
    int a_num;
};
set<int> C;

node N[MAXVERTEX];
bool v_in_c[MAXVERTEX];
int edge[MAXVERTEX][MAXVERTEX];     // edge[u][v] 表示u v之间的连边，若没有边则设为0

struct Edg {
    int coverd;
    int node1;
    int node2;
    // WZY: list node.
    Edg * prev;
    Edg * succ;
};



//int visited[MAXEDGE];
int w[MAXEDGE];
Edg myedge[MAXEDGE];
int dscore[MAXEDGE];

// WZY: use double link to maintian L and UL
struct List {
    Edg * head;
    Edg * unchecked;
    int size;
    List() {
        size = 0;
        head = new Edg();
        unchecked = head;
        head->prev = nullptr;
        head->succ = nullptr;
    }
    void insert(Edg *);
    void remove(Edg *);
    bool empty();
    void update(int, int);
}L;
void List::insert(Edg * e) {
    if (head->succ) {
        e->succ = head->succ;
        head->succ->prev = e;
    }
    else {  // e是L中第一条边
        e->succ = nullptr;
        unchecked = e;      // 初始状态下，UL指针指向L中最后一个边，也就是第一个插入的边
    }
    head->succ = e;
    e->prev = head;
    size ++;
}
void List::remove(Edg *e) {
    e->prev->succ = e->succ;
    e->succ->prev = e->prev;
    if (unchecked == e) {   // 保证UL指针始终在L里面
        unchecked = e->prev;
    }
    size --;
}
bool List::empty() {
    return head->succ ? false : true;
}
void List::update(int addv, int removev) {
    if (addv != -1) {
        for (int i = 0; i < N[addv].edge.size(); ++i) {
            int e = N[addv].edge[i];
            if (!myedge[e].coverd) {    // 原来未覆盖的边变成覆盖
                myedge[e].coverd = true;
                remove(&myedge[e]);
            }
        }
    }
    if (removev != -1) {
        for (int i = 0; i < N[removev].edge.size(); ++i) {
            int e = N[removev].edge[i];
            if (myedge[e].coverd) {     // 原来覆盖的边变成未覆盖
                myedge[e].coverd = false;
                insert(&myedge[e]);
            }
        }
    }
}

void add(int v)
{
    C.insert(v);
    v_in_c[v] = 1;
    dscore[v] = -dscore[v]; // update dscore.
    int i,e,n;
    
    int edge_count = N[v].edge.size();
    
    for (i=0; i<edge_count; ++i)
    {
        e = N[v].edge[i];
        n = myedge[e].node1 == v ? myedge[e].node2 : myedge[e].node1;
        
        if (v_in_c[n] == 0)//this adj isn't in cover set
        {
            dscore[n] -= 2 * w[e];
        }
        else
        {
            dscore[n] += 2 * w[e];
        }
    }
}

void remove(int v)
{
    v_in_c[v] = 0;
    dscore[v] = -dscore[v];
    //conf_change[v] = 0;
    
    int i,e,n;
    int edge_count = N[v].edge.size();
    for (i=0; i < edge_count; ++i)
    {
        e = N[v].edge[i];
        n = myedge[e].node1 == v ? myedge[e].node2 : myedge[e].node1;
        
        if (v_in_c[n]==0)//this adj isn't in cover set
        {
            dscore[n] += 2 * w[e];
        }
        else
        {
            dscore[n] -= 2 * w[e];
        }
    }
}
int score(int u, int v) { // score(u, v) = cost(G, C) - cost(G, C'). C' = C\{u} + {v}.
    int s = dscore[u] + dscore[v];
    if (edge[u][v] > 0) {
        s += w[edge[u][v]];
    }
    return s;
}

// ChooseExchangePair是选取合适的交换顶点(u, v)的函数，返回一对顶点(u, v)，表示删去C中的顶点u，并将v加入C中。
// 返回(0, 0)说明当前没有合适的顶点，即C已经达到局部最优（但不一定是全局最优，因此需要通过随机处理打破平衡）
// 对于点对(u, v)同样定义权值函数score(u, v)来决定是否交换他们。
// score(u, v) = cost(G, C) - cost(G, C'). C' = C\{u} + {v}.

pair<int, int> ChooseExchangePair() {
    // S表示可交换的顶点集
    set<pair <int, int> > S;
    /* 构造集合S，将满足以下条件的（u,v）加入集合S中：u属于当前的覆盖集C，v属于边集L中年龄最大的边的两个端点，score（u,v）>0 */
    int token = 0;
    int max = 0;
    int i;
    for (i = 0; i < edge_num; i++) {
        if (myedge[i].coverd == 0) {
            continue;
        }
        if (w[i] > max) {
            max = w[i];
            token = i;
        }
    }
    if (token != 0) {
        for (set<int>::iterator it = C.begin(); it != C.end(); it++) {
            if (score(*it, myedge[token].node1) > 0) {
                S.insert(make_pair(*it, myedge[token].node1));
            }
            if (score(*it, myedge[token].node2) > 0) {
                S.insert(make_pair(*it, myedge[token].node1));
            }
        }
    }
    if (S.size() != 0) {
        // 从S中随机挑一个
        if (*S.begin() != make_pair(tabuRemove, tabuAdd)) {
            return *S.begin();
        }
        else {
            if (*S.end() != make_pair(tabuRemove, tabuAdd)) {
                return *S.end();
            }
        }
    }
    // 当L中年龄最大的边不满足条件时，从UL中按照年龄从大到小搜索
    /* 对UL按照年龄大小排序*/
    while (L.unchecked != L.head) {
        Edg * it = L.unchecked;
        L.unchecked = L.unchecked->prev;
        for (set<int>::iterator it2 = C.begin(); it2 != C.end(); it2++) {
            if (score(*it2, it->node1) > 0) {
                S.insert(make_pair(*it2, it->node1));
            }
            if (score(*it2, it->node2) > 0) {
                S.insert(make_pair(*it2, it->node2));
            }
        }
        if (S.size() != 0) {
            // 从S中随机挑一个
            if (*S.begin() != make_pair(tabuRemove, tabuAdd)) {
                return *S.begin();
            }
            else {
                if (*S.end() != make_pair(tabuRemove, tabuAdd)) {
                    return *S.end();
                }
            }
        }
    }
    
    //如果L和UL都找不出，就返回（0,0）
    return make_pair(0, 0);
}

set<int> CC;
void buildC() {
    int temp;
    for (int i = 0; i < edge_num; i++) {
        if (myedge[i].coverd == 0) {
            if (N[myedge[i].node1].a_num > N[myedge[i].node2].a_num) {
                temp = myedge[i].node1;
            }
            else {
                temp = myedge[i].node2;
            }
//            C.insert(temp);
            add(temp);
            for (int j = 0; j < N[temp].edge.size(); j++) { // cover it
                myedge[N[temp].edge[j]].coverd = 1;
            }
            N[temp].a_num = 0;
        }
    }
}

set<int> EWLS() {
    int step = 0;
    for (int i = 0; i < edge_num; i++) {
        L.update(i, -1);
        myedge[i].coverd = false;
    }
    C.clear();
    buildC();
    int ub = C.size();
    set<int> CFinal = C;
    int max = -999999;
    int res = -1;
    for (int i = 0; i < delta; i++) {
        max = -999999;
        for (set<int>::iterator it = C.begin(); it != C.end(); it++) {
            if (dscore[*it] > max) {
                max = dscore[*it];
                res = *it;
            }
        }
//        C.erase(res);
        remove(res);
        L.update(-1, res);
    }
    
    
    while (step < maxSteps) {
        pair<int, int> exchangePair;
        if ((exchangePair = ChooseExchangePair()) != make_pair(0, 0)) {
            int u = exchangePair.first;
            int v = exchangePair.second;
//            C.erase(u);
//            C.insert(v);
            remove(u);
            add(v);
            tabuAdd = u;
            tabuRemove = v;
            L.update(v, u);
        }
        else {
            int k = 0;
            for (int i = 0; i < edge_num; i++) {
                if (!myedge[i].coverd) {
                    w[i]++;
                    k = i;
                }
            }
            set<int>::iterator it = C.end();
//            C.erase(*it);
//            C.insert(myedge[k].node1);
            remove(*it);
            add(myedge[k].node1);
            L.update(myedge[k].node1, *it);
        }
        if (C.size() + L.size < ub) {
            ub = C.size() + L.size;
            // update_UL();
            if (L.empty()) CFinal = C;
            else {
                CC = C;
                buildC();
                CFinal = C;
                C = CC;
            }
            for (int i = 0; i < C.size() - (ub - delta); i++) {
                max = -999999;
                for (set<int>::iterator it = C.begin(); it != C.end(); it++) {
                    if (dscore[*it] > max) {
                        max = dscore[*it];
                        res = *it;
                    }
                }
//                C.erase(res);
                remove(res);
                L.update(-1, res);
            }
        }
        step++;
    }
    return CFinal;
}
void buildInstance(int n, int m) {
// 初始化图
    
}
int main() {
    int n, m;
    while (scanf("%d%d", &n, &m)) {
        buildInstance(n, m);
        set<int> S = EWLS();
        printf("%d\n", (int)S.size());
        for (auto & r : S) {
            printf("%d ", r);
        }
        printf("\n");
    }
    return 0;
}

