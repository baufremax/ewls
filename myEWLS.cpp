#include <cstdio>
#include <cstring>
#include <cmath>
#include <utility>
#include <vector>
#include <set>
#include <algorithm>

using namespace std;
const int MAXEDGE = 260000;
const int MAXVERTEX =  800;
int edge_num;
int node_num;

int tabuAdd, tabuRemove;
int delta = 1;
int maxSteps = 10;

struct node {
    vector<int> edge;
    node() { }
    int a_num;
};
set<int> C;

node N[MAXVERTEX];
bool G[MAXVERTEX][MAXVERTEX];       // 邻接矩阵
bool v_in_c[MAXVERTEX];
bool v_in_s[MAXVERTEX];         // v 是否在点覆盖S中
int edge[MAXVERTEX][MAXVERTEX];     // edge[u][v] 表示u v之间的连边，若没有边则设为-1

struct Edg {
    bool coverd;
    int node1;
    int node2;
    int w;
    // WZY: list node.
    Edg * prev;
    Edg * succ;
    void init(int u, int v) {
        node1 = u;
        node2 = v;
        coverd = false;
        prev = nullptr;
        succ = nullptr;
        w = 1;
    }
    Edg() {
        coverd = false;
        prev = nullptr;
        succ = nullptr;
        w = 1;
    }
    Edg(int u, int v) : node1(u), node2(v) {
        coverd = false;
        prev = nullptr;
        succ = nullptr;
        w = 1;
    }
};

int w[MAXEDGE];
Edg myedge[MAXEDGE];
int dscore[MAXEDGE];

// use double list to maintian L and UL
struct List {
    Edg * head;
    Edg * tail;
    Edg * unchecked;
    int size;
    List() {
        size = 0;
        head = new Edg();
        tail = new Edg();
        unchecked = head;
        head->prev = nullptr;
        head->succ = tail;
        tail->prev = head;
        tail->succ = nullptr;
    }
    void init();
    void insert(Edg *);
    void remove(Edg *);
    bool empty();
    void update(int, int);
    ~List() {
        if (head) {
            delete head;
        }
        if (tail) {
            delete tail;
        }
    }
};
void List::init() {
    size = 0;
    head->prev = nullptr;
    head->succ = tail;
    tail->prev = head;
    tail->succ = nullptr;
}
void List::insert(Edg * e) {
    if (head->succ != tail) {
        e->succ = head->succ;
        head->succ->prev = e;
    }
    else {  // e是L中第一条边
        e->succ = tail;
        tail->prev = e;
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
    return size ? true : false;
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
            int v1 = myedge[e].node1;
            int v2 = myedge[e].node2;
            if (myedge[e].coverd && v_in_c[v1] == 0 && v_in_c[v2] == 0) {
                // 原来覆盖的边变成未覆盖
                myedge[e].coverd = false;
                insert(&myedge[e]);
            }
        }
    }
}
List L;

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
            dscore[n] -= myedge[e].w;
        }
        else
        {
            dscore[n] += myedge[e].w;
        }
        //        myedge[e].coverd = true;        // cover the edge.
    }
}

void remove(int v)
{
    C.erase(v);
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
            dscore[n] += myedge[e].w;
            //            myedge[e].coverd = false;   // not covered now.
        }
        else
        {
            dscore[n] -= myedge[e].w;
        }
    }
}
int score(int u, int v) { // score(u, v) = cost(G, C) - cost(G, C'). C' = C\{u} + {v}.
    int s = dscore[u] + dscore[v];
    if (edge[u][v] >= 0) {
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
    
    Edg * token = L.tail->prev; // L中最后一个边就是age最大的边
    if (token != L.head) {  // token exists.
        for (set<int>::iterator it = C.begin(); it != C.end(); it++) {
            if (score(*it, token->node1) > 0) {
                S.insert(make_pair(*it, token->node1));
            }
            if (score(*it, token->node2) > 0) {
                S.insert(make_pair(*it, token->node2));
            }
        }
    }
    if (S.size() != 0) {
        // 从S中随机挑一个
        // int randSub = rand() % S.size();
        // auto it(S.begin());
        // advance(it, randSub);
        // return * it;
        if (*S.begin() != make_pair(tabuRemove, tabuAdd)) {
            return *S.begin();
        }
        else {
            if (*S.rbegin() != make_pair(tabuRemove, tabuAdd)) {
                return *S.rbegin();
            }
        }
    }
    // 当L中年龄最大的边不满足条件时，从UL中按照年龄从大到小搜索(也就是从后到前)
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
                if (*S.rbegin() != make_pair(tabuRemove, tabuAdd)) {
                    return *S.rbegin();
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
            int v1 = myedge[i].node1;
            int v2 = myedge[i].node2;
            if (v_in_c[v1]) {
                temp = v2;
            }
            else {
                temp = v1;
            }
            // C.insert(temp);
            add(temp);
            L.update(temp, -1);
            // for (int j = 0; j < N[temp].edge.size(); j++) { // cover it
            //     myedge[N[temp].edge[j]].coverd = 1;
            // }
            N[temp].a_num = 0;
        }
    }
}

void expandC() {    // 扩充C使得C能覆盖L中所有边，注意扩充的顶点在计入CFinal后即立刻删去，因此不需要更新coverd
    Edg * p = L.tail->prev;
    while (p != L.head) {   // 将L中所有边都覆盖
        int v1 = p->node1;
        int v2 = p->node2;
        p = p->prev;
        if (v_in_c[v1] == 0 && v_in_c[v2] == 0) {
            int v1d = N[v1].edge.size();  // v1连边个数
            int v2d = N[v2].edge.size();
            if (v1d > v2d) {
                C.insert(v1);
                v_in_c[v1] = 1;
            }
            else {
                C.insert(v2);
                v_in_c[v2] = 1;
            }
        }
    }
}

void update_v_in_c() {      // 重置v_in_c 即标记C中顶点
    memset(v_in_c, 0, sizeof(v_in_c));
    for (auto & i : C) {
        v_in_c[i] = 1;
    }
}

set<int> EWLS() {
    int step = 0;
    for (int i = 0; i < edge_num; i++) {
        L.insert(&myedge[i]);
        //        myedge[i].coverd = false;
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
    
    while (step < maxSteps * node_num) {
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
            Edg * p = L.head->succ;
            Edg * k = p;
            while(p != L.tail) {
                if (!p->coverd) {
                    p->w++;
                    // 更新w(e)的同时要更新dscore
                    int v1 = p->node1;
                    int v2 = p->node2;
                    dscore[v1]++;
                    dscore[v2]++;
                    k = p;
                }
                p  = p->succ;
            }
            // int randSub = rand() % C.size();
            // set<int>::const_iterator it(C.begin());
            // advance(it, randSub);
            // int dv = *it;
            int dv = *C.rbegin();
            //            C.erase(*it);
            //            C.insert(myedge[k].node1);
            remove(dv);
            add(k->node1);
            L.update(k->node1, dv);
        }
        if (C.size() + L.size < ub) {
            ub = C.size() + L.size;
            // update_UL();
            if (L.empty()) CFinal = C;
            else {
                CC = C;
                // buildC();
                expandC();
                ub = C.size();      // update ub.(一个顶点v可能覆盖L中多条边 所以ub可以进一步改进)
                CFinal = C;
                C = CC;
                update_v_in_c();
            }
            int decNum = C.size() - (ub - delta);
            if (ub <= delta) {
                decNum = 1;
            }
            for (int i = 0; i < decNum; i++) {
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
    node_num = n;
    edge_num = 0;
    C.clear();
    memset(v_in_c, 0, sizeof(v_in_c));
    memset(v_in_s, 0, sizeof(v_in_s));
    for (int i = 0; i < MAXVERTEX; ++i) {
        for (int j = 0; j < MAXVERTEX; ++j) {
            edge[i][j] = -1;
            G[i][j] = 1;
        }
    }
    L.init();
    for (int i = 0; i < MAXVERTEX; ++i) {
        N[i].edge.clear();
    }
    // 求补图
    for (int i = 0; i < m; ++i) {
        int u, v;
        scanf("%d %d", &u, &v);
        G[u][v] = G[v][u] = 0;
    }
    for (int u = 1; u <= n; ++u) {
        for (int v = u + 1; v <= n; ++v) {
            if (G[u][v] == 1) {
                int i = edge_num;
                edge[u][v] = edge[v][u] = i;
                myedge[i].init(u, v);
                w[i] = 1;
                N[u].edge.push_back(i);
                N[v].edge.push_back(i);
                edge_num ++;
            }
        }
    }
    for (int i = 1; i <= n; ++i){
        dscore[i] = N[i].edge.size();// 初始dscore[v]即v上连边数
    }
}
int main() {
    int n, m;
    while (scanf("%d%d", &n, &m) != EOF) {
        buildInstance(n, m);
        set<int> S = EWLS();
        printf("%d\n", n - (int)S.size());
        for (auto & r : S) {
            v_in_s[r] = true;
        }
        // 最小点覆盖的余集就是最大团
        for (int i = 1; i <= n; ++i) {
            if (!v_in_s[i]) {
                printf("%d ", i);
            }
        }
        printf("\n");
    }
    return 0;
}

