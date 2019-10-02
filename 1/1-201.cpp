#include <stdio.h>
#include <iostream>
#include <algorithm>
#include <cstring>
#include <set>
#include <map>
using namespace std;
const int MaxL = 16, N = 5005;
char buf[1 << 20], *p1, *p2;
#define GC (p1 == p2 && (p2 = (p1 = buf) + fread(buf, 1, 1 << 20, stdin), p1 == p2) ? 0 : *p1++)
inline int _R() {
    char t = GC;
    int x;
    while (t < 48 || t > 57) t = GC;
    for (x = 0; t > 47 && t < 58; t = GC) x = (x << 3) + (x << 1) + t - 48;
    return x;
}
inline int Rand() {
    static unsigned int seed = 998244353;
    return seed = (seed ^ 1313131311) * 1234321237;
}
int n, m;
struct Graph {
    set<int> mt[N];
    void add(int x, int y) {
        mt[x].insert(y);
        mt[y].insert(x);
    }
    void del(int x, int y) {
        mt[x].erase(y);
        mt[y].erase(x);
    }
    bool find(int x, int y) { return mt[x].count(y); }
    bool empty(int x) { return mt[x].empty(); }
} G[MaxL];
struct node {
    node *ls, *rs, *fa;
    bool hav;
    int pid, tid, sz, w;
} pool[10000000], *bin[10000000], *null;
int tl;
void Init() {
    null = pool;
    null->ls = null->rs = null->fa = null;
    for (int i = 1; i < N * MaxL; i++) bin[i] = pool + i;
}
struct ETT {
    Graph *G;
    int tote;
    set<int> e[N];
    map<int, int> mt[N];
    node *End[2000005], *id[N];
    node *newnode(int id, int tid) {
        node *x = bin[++tl];
        x->pid = id;
        x->tid = tid;
        x->hav = id && !G->empty(id);
        x->sz = 1;
        x->ls = x->rs = x->fa = null;
        return x;
    }
    void delnode(node *x) { bin[tl--] = x; }  //回收节点
    void pushup(node *x) {
        x->hav = (x->pid && !G->empty(x->pid)) || x->ls->hav || x->rs->hav;
        x->sz = x->ls->sz + x->rs->sz + 1;
    }
    void splitup(node *x, node *&l, node *&r) {
        if (x->fa == null)
            return;
        node *y = x->fa;
        x->fa = null;
        if (y->ls == x) {
            y->ls = r;
            r->fa = y;
            pushup(y);
            r = y;
        } else {
            y->rs = l;
            l->fa = y;
            pushup(y);
            l = y;
        }
        splitup(y, l, r);
    }
    void split(node *x, node *&l, node *&r) {  //把x分离出来，l存前缀，r存后缀
        l = x->ls;
        r = x->rs;
        x->ls = x->rs = l->fa = r->fa = null;  //左右清空
        pushup(x);
        splitup(x, l, r);
    }
    node *merge(node *l, node *r) {  // l真权值小
        if (l == null)
            return r;
        if (r == null)
            return l;
        if (Rand() & 16) {
            l->rs = merge(l->rs, r);
            l->rs->fa = l;
            return pushup(l), l;
        } else {
            r->ls = merge(l, r->ls);
            r->ls->fa = r;
            return pushup(r), r;
        }
    }
    void makeroot(node *&x) {  //
        if (x == null)
            return;
        node *l, *r;
        split(x, l, r);
        x = merge(merge(x, r), l);
    }
    node *findrt(node *x) {
        while (x->fa != null) x = x->fa;
        while (x->ls != null) x = x->ls;
        return x;
    }
    node *findrt(int x) { return findrt(id[x]); }
    void add(int u, int v, bool lev) {  // lev是为了节省空间的
        node *x = id[u], *y = id[v];
        if (x != null && y != null && findrt(x) == findrt(y)) {  //如果已经连过了
            pushup(x);
            pushup(y);
            while (x->fa != null) x = x->fa, pushup(x);
            while (y->fa != null) y = y->fa, pushup(y);
            return;
        }
        // u,v至少有一个未在图中
        makeroot(x);
        makeroot(y);                                                   //非空的转根 将(0,u) 转根
        End[++tote] = newnode(x == null ? u : 0, u), mt[u][v] = tote;  //没有u，则(u,u) ，否则(0,u)
        End[++tote] = newnode(y == null ? v : 0, v), mt[v][u] = tote;
        if (lev)
            e[u].insert(v), e[v].insert(u);  // e是存在于树中的邻点
        merge(merge(merge(End[tote - 1], y), End[tote]), x);
        if (x == null)
            id[u] = End[tote - 1];  // id表示第一次出现的位置
        if (y == null)
            id[v] = End[tote];
    }
    void getid(int x) {
        if (mt[x].empty()) {
            id[x] = null;
            return;
        }  // x无任何连接点了
        id[x] = End[mt[x].begin()->second];
        node *l, *r;
        split(id[x], l, r);
        id[x]->pid = x;  //?
        pushup(id[x]);
        merge(merge(id[x], r), l);
    }
    int del(int u, int v) {
        int eid = mt[u][v];
        mt[u].erase(v);
        mt[v].erase(u);  //邻接表
        node *x = End[eid], *y = End[eid ^ 1], *l, *r;
        split(x, l, r);
        merge(r, l);
        split(y, l, r);
        int t0 = l->sz, t1 = r->sz;
        if (x->pid)
            getid(u);  ////如果删除了第一个点则需要把第二个点设为第一个点
        if (y->pid)
            getid(v);
        delnode(x);
        delnode(y);
        return t1 < t0 ? u : v;
    }
    void init(int x) {
        tote = 1;
        fill(id, id + n + 1, null);
        G = ::G + x;  // G里放的是G[x]
    }
} T[MaxL];
namespace D_Graph {
void addlevel(int level,
              node *x) {  //整棵树有效边全部+1真升(非虚边，e为实边 mt为所有边) 把相邻结点删掉了e 但是边没变
    if (x == null || !x->hav)
        return;    //无实点退出
    if (x->pid) {  // x是实点
        int u = x->pid;
        for (auto v : T[level].e[u]) {
            if (u >= v)
                continue;  //保证只考虑一次
            G[level].del(u, v);
            G[level + 1].add(u, v);
            T[level + 1].add(u, v, 1);
        }
        T[level].e[u].clear();
    }
    addlevel(level, x->ls);
    addlevel(level, x->rs);
    T[level].pushup(x);
}
node *xrt;
int X, Y;
bool findin_G(int level, int x) {
    while (!G[level].empty(x)) {          //跟x相邻的点
        int u = *G[level].mt[x].begin();  //遍历边
        if (T[level].findrt(u) != xrt)
            return X = x, Y = u, 1;  //另一端点在另一棵树内(不限制哪棵树)，upd：其实是限制那棵树的
                                     //只不过仅有一棵可能的树能到达
        G[level].del(x, u);
        G[level + 1].add(x, u);
        T[level + 1].add(x, u, 1);  //
    }
    return 0;
}
bool findin_T(int level, node *x) {  //每一个点找相邻的看是否能到达另一棵树
    if (x == null || !x->hav)
        return 0;
    if (x->pid)
        if (findin_G(level, x->pid))
            return 1;
    if (findin_T(level, x->ls))
        return 1;
    if (findin_T(level, x->rs))
        return 1;
    x->hav = 0;
    return 0;  //无用的点打个标记 其子树与外界不联通
}
void find_replacement(int level, int x) {  // level
    node *p = T[level].id[x];
    xrt = p;
    if (p == null)
        findin_G(level, x);  //无实边
    else
        T[level].makeroot(p), addlevel(level, p),
            findin_T(level, p);  //树边全真升且原树T样子 因为树T+1为树T的真子集 但为平衡复杂度树T的e删除
}
void add(int x, int y) {  //加边
    G[0].add(x, y);
    T[0].add(x, y, 1);
}
void del(int x, int y) /*删边*/ {
    for (int i = MaxL - 1; i >= 0; i--) {
        if (!G[i].find(x, y))
            continue;    // G为图
        G[i].del(x, y);  //
        if (!T[i].mt[x].count(y))
            return;  //第一个G中找到边的 如果该边不存在于T 其他的T肯定也不存在
        T[i].e[x].erase(y);
        T[i].e[y].erase(x);
        X = Y = 0;
        for (int j = i; j >= 0; j--) {
            int t = T[j].del(x, y);  //假如已经找到代替的边了 不需要添加连接点 直接连边
            if (!X) {
                find_replacement(j, t);  //找条虚边
                if (X)
                    T[j].add(X, Y, 1);
            } else
                T[j].add(X, Y, 0);  //这里还没删边
        }
        return;  //*
    }
}
bool isconnected(int x, int y) {
    return T[0].id[x] != null && T[0].id[y] != null && T[0].findrt(x) == T[0].findrt(y);
}
}  // namespace D_Graph
int main() {
    int i, opt, x, y, ans = 0;
    n = _R();
    m = _R();
    Init();
    for (i = 0; i < MaxL; i++) T[i].init(i);
    for (i = 1; i <= m; i++) {
        opt = _R();
        x = _R() ^ ans;
        y = _R() ^ ans;
        if (opt == 0)
            D_Graph::add(x, y);
        else if (opt == 1)
            D_Graph::del(x, y);
        else {
            ans = D_Graph::isconnected(x, y);
            puts(ans ? "Y" : "N");
            ans = ans ? x : y;
        }
    }
}