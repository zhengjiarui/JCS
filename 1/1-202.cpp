#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <bitset>
#include <set>
#include <map>
#include <vector>
#include <stack>
#include <queue>
using namespace std;
#define MAXN 5010
#define MAXM 15
#define MAXE 1000010
#define INF 1000000000
#define MOD 1000000007
#define eps 1e-8
#define ll long long
struct lb {
    int tai[MAXN], fro[MAXE], nxt[MAXE];
    void add(int x, int y) {
        fro[y] = tai[x];
        nxt[tai[x]] = y;
        nxt[y] = 0;
        tai[x] = y;
    }
    void del(int x, int y) {
        if (!nxt[y]) {
            tai[x] = fro[y];
        } else {
            fro[nxt[y]] = fro[y];
        }
        if (fro[y]) {
            nxt[fro[y]] = nxt[y];
        }
        fro[y] = nxt[y] = 0;
    }
};
struct LCT {
    int fa[MAXN], son[MAXN][2], siz[MAXN], Siz[MAXN];
    int blk[MAXN], sum[MAXN], Sum[MAXN];
    int blkt[MAXN], sumt[MAXN], Sumt[MAXN];
    int srt[MAXN];
    bool rev[MAXN];
    int lv[MAXN], rv[MAXN];
    lb vec, vect;
    int st[MAXN], tp;
    lb ls, lst;
    LCT() {
        int i;
        for (i = 1; i < MAXN; i++) {
            srt[i] = i;
            ud(i);
        }
    }
    inline void ud(int x) {
        siz[x] = siz[son[x][0]] + siz[son[x][1]] + Siz[x] + 1;
        sum[x] = sum[son[x][0]] + sum[son[x][1]] + Sum[x] + blk[x];
        sumt[x] = sumt[son[x][0]] + sumt[son[x][1]] + Sumt[x] + blkt[x];
        lv[x] = son[x][0] ? lv[son[x][0]] : x;
        rv[x] = son[x][1] ? rv[son[x][1]] : x;
    }
    inline void torev(int x) {
        if (!x) {
            return;
        }
        rev[x] ^= 1;
        swap(son[x][0], son[x][1]);
        swap(lv[x], rv[x]);
        srt[lv[x]] = srt[rv[x]];
    }
    inline void pd(int x) {
        if (rev[x]) {
            torev(son[x][0]);
            torev(son[x][1]);
            rev[x] = 0;
        }
    }
    inline void apd(int x) {
        int i;
        st[++tp] = x;
        for (i = x; !ir(i); i = fa[i]) {
            st[++tp] = fa[i];
        }
        for (; tp; tp--) {
            pd(st[tp]);
        }
    }
    inline bool ir(int x) { return son[fa[x]][0] != x && son[fa[x]][1] != x; }
    inline void cot(int x, int y, bool z) {
        if (x) {
            fa[x] = y;
        }
        if (y) {
            son[y][z] = x;
        }
    }
    inline void rot(int x, bool z) {
        int xx = fa[x], xxx = fa[xx];
        cot(son[x][z], xx, z ^ 1);
        if (ir(xx)) {
            fa[x] = xxx;
        } else {
            cot(x, xxx, son[xxx][1] == xx);
        }
        cot(xx, x, z);
        ud(xx);
    }
    void splay(int x) {
        apd(x);
        while (!ir(x)) {
            int xx = fa[x], xxx = fa[xx];
            if (ir(xx)) {
                rot(x, son[xx][0] == x);
            } else {
                bool z = son[xxx][0] == xx;
                if (son[xx][z] == x) {
                    rot(x, z ^ 1);
                    rot(x, z);
                } else {
                    rot(xx, z);
                    rot(x, z);
                }
            }
        }
        ud(x);
        srt[lv[x]] = srt[rv[x]] = x;
    }
    inline void acs(int x) {
        int t = 0;
        while (x) {
            splay(x);
            Siz[x] += siz[son[x][1]];
            Sum[x] += sum[son[x][1]];
            Sumt[x] += sumt[son[x][1]];
            srt[lv[son[x][1]]] = son[x][1];
            if (sum[son[x][1]]) {
                ls.add(x, lv[son[x][1]]);
            }
            if (sumt[son[x][1]]) {
                lst.add(x, lv[son[x][1]]);
            }
            son[x][1] = t;
            Siz[x] -= siz[son[x][1]];
            Sum[x] -= sum[son[x][1]];
            Sumt[x] -= sumt[son[x][1]];
            if (sum[son[x][1]]) {
                ls.del(x, lv[son[x][1]]);
            }
            if (sumt[son[x][1]]) {
                lst.del(x, lv[son[x][1]]);
            }
            ud(x);
            t = x;
            x = fa[x];
        }
    }
    inline void setroot(int x) {
        acs(x);
        splay(x);
        torev(x);
        pd(x);
    }
    inline void link(int x, int y) {
        setroot(x);
        setroot(y);
        fa[x] = y;
        Siz[y] += siz[x];
        Sum[y] += sum[x];
        Sumt[y] += sumt[x];
        if (sum[x]) {
            ls.add(y, lv[x]);
        }
        if (sumt[x]) {
            lst.add(y, lv[x]);
        }
        ud(x);
        ud(y);
    }
    inline void cut(int x, int y) {
        setroot(x);
        acs(y);
        splay(y);
        son[y][0] = fa[x] = 0;
        ud(y);
        srt[x] = x;
        srt[y] = y;
    }
    int rt(int x) {
        acs(x);
        splay(x);
        pd(x);
        return lv[x];
    }
    inline bool sr(int x, int y) { return rt(x) == rt(y); }
    int size(int x) {
        setroot(x);
        splay(x);
        return siz[x];
    }
    int find(int x) {
        if (blk[x]) {
            acs(x);
            return x;
        }
        if (Sum[x]) {
            return find(srt[ls.tai[x]]);
        }
        if (sum[son[x][0]]) {
            return find(son[x][0]);
        }
        if (sum[son[x][1]]) {
            return find(son[x][1]);
        }
        return 0;
    }
    int findt(int x) {
        if (blkt[x]) {
            acs(x);
            return x;
        }
        if (Sumt[x]) {
            return findt(srt[lst.tai[x]]);
        }
        if (sumt[son[x][0]]) {
            return findt(son[x][0]);
        }
        if (sumt[son[x][1]]) {
            return findt(son[x][1]);
        }
        return 0;
    }
    void toblk(int x) {
        if (blk[x]) {
            return;
        }
        setroot(x);
        splay(x);
        blk[x] = 1;
        ud(x);
    }
    void towht(int x) {
        if (!blk[x]) {
            return;
        }
        setroot(x);
        splay(x);
        blk[x] = 0;
        ud(x);
    }
    void toblkt(int x) {
        if (blkt[x]) {
            return;
        }
        setroot(x);
        splay(x);
        blkt[x] = 1;
        ud(x);
    }
    void towhtt(int x) {
        if (!blkt[x]) {
            return;
        }
        setroot(x);
        splay(x);
        blkt[x] = 0;
        ud(x);
    }
};
LCT mst[MAXM];
int L = MAXM - 1;
map<pair<int, int>, int> lev;
map<pair<int, int>, bool> ontree;
int la;
map<pair<int, int>, int> num;
int E;
int M;
int v1[MAXE], v2[MAXE];
int main() {
    // freopen("ex_negiizhao_1.in","r",stdin);
    int i, j, o, x, y, u, v;
    int tmp;
    scanf("%*d%d", &tmp);
    M = tmp;
    while (tmp--) {
        scanf("%d%d%d", &o, &x, &y);
        x ^= la;
        y ^= la;
        int tx = x, ty = y;
        x++;
        y++;
        if (x > y) {
            swap(x, y);
        }
        if (o == 0) {
            num[make_pair(x, y)] = ++E;
            v1[E] = v1[E + M] = x;
            v2[E] = v2[E + M] = y;
            int e = E;
            lev[make_pair(x, y)] = L;
            mst[L].toblk(x);
            mst[L].toblk(y);
            mst[L].vec.add(x, e);
            mst[L].vec.add(y, e + M);
            if (!mst[L].sr(x, y)) {
                mst[L].link(x, y);
                ontree[make_pair(x, y)] = 1;
                mst[L].toblkt(x);
                mst[L].toblkt(y);
                mst[L].vect.add(x, e);
                mst[L].vect.add(y, e + M);
            } else {
                ontree[make_pair(x, y)] = 0;
            }
        }
        if (o == 1) {
            int l = lev[make_pair(x, y)];
            int e = num[make_pair(x, y)];
            lev[make_pair(x, y)] = 0;
            mst[l].vec.del(x, e);
            mst[l].vec.del(y, e + M);
            if (!mst[l].vec.tai[x]) {
                mst[l].towht(x);
            }
            if (!mst[l].vec.tai[y]) {
                mst[l].towht(y);
            }
            if (ontree[make_pair(x, y)]) {
                mst[l].vect.del(x, e);
                mst[l].vect.del(y, e + M);
                if (!mst[l].vect.tai[x]) {
                    mst[l].towhtt(x);
                }
                if (!mst[l].vect.tai[y]) {
                    mst[l].towhtt(y);
                }
                ontree[make_pair(x, y)] = 0;
                for (i = l; i <= L; i++) {
                    mst[i].cut(x, y);
                }
                for (i = l; i <= L; i++) {
                    if (mst[i].size(x) > mst[i].size(y)) {
                        swap(x, y);
                    }
                    while (1) {
                        mst[i].setroot(x);
                        mst[i].splay(x);
                        if (u = mst[i].findt(x)) {
                            int tu = u;
                            for (int it = mst[i].vect.tai[u]; it;) {
                                int v = (v1[it] == u) ? v2[it] : v1[it];
                                int ee = it;
                                it = mst[i].vect.fro[it];
                                int u = tu;
                                if (u > v) {
                                    swap(u, v);
                                }
                                if (ee > M) {
                                    ee -= M;
                                }
                                lev[make_pair(u, v)] = i - 1;
                                mst[i].vec.del(u, ee);
                                mst[i].vec.del(v, ee + M);
                                if (!mst[i].vec.tai[u]) {
                                    mst[i].towht(u);
                                }
                                if (!mst[i].vec.tai[v]) {
                                    mst[i].towht(v);
                                }
                                mst[i].vect.del(u, ee);
                                mst[i].vect.del(v, ee + M);
                                if (!mst[i].vect.tai[u]) {
                                    mst[i].towhtt(u);
                                }
                                if (!mst[i].vect.tai[v]) {
                                    mst[i].towhtt(v);
                                }
                                mst[i - 1].toblk(u);
                                mst[i - 1].toblk(v);
                                mst[i - 1].vec.add(u, ee);
                                mst[i - 1].vec.add(v, ee + M);
                                mst[i - 1].toblkt(u);
                                mst[i - 1].toblkt(v);
                                mst[i - 1].vect.add(u, ee);
                                mst[i - 1].vect.add(v, ee + M);
                                mst[i - 1].link(u, v);
                            }
                        } else {
                            break;
                        }
                    }
                    while (1) {
                        mst[i].setroot(x);
                        mst[i].splay(x);
                        if (u = mst[i].find(x)) {
                            bool flag = 0;
                            int tu = u;
                            for (int it = mst[i].vec.tai[u]; it;) {
                                int v = (v1[it] == u) ? v2[it] : v1[it];
                                int ee = it;
                                it = mst[i].vec.fro[it];
                                int u = tu;
                                if (u > v) {
                                    swap(u, v);
                                }
                                if (ee > M) {
                                    ee -= M;
                                }
                                if (mst[i].sr(u, v)) {
                                    lev[make_pair(u, v)] = i - 1;
                                    mst[i].vec.del(u, ee);
                                    mst[i].vec.del(v, ee + M);
                                    if (!mst[i].vec.tai[u]) {
                                        mst[i].towht(u);
                                    }
                                    if (!mst[i].vec.tai[v]) {
                                        mst[i].towht(v);
                                    }
                                    mst[i - 1].toblk(u);
                                    mst[i - 1].toblk(v);
                                    mst[i - 1].vec.add(u, ee);
                                    mst[i - 1].vec.add(v, ee + M);
                                } else {
                                    flag = 1;
                                    ontree[make_pair(u, v)] = 1;
                                    mst[i].toblkt(u);
                                    mst[i].toblkt(v);
                                    mst[i].vect.add(u, ee);
                                    mst[i].vect.add(v, ee + M);
                                    for (; i <= L; i++) {
                                        mst[i].link(u, v);
                                    }
                                    break;
                                }
                            }
                            if (flag) {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
        }
        if (o == 2) {
            if (mst[L].sr(x, y)) {
                puts("Y");
                la = tx;
            } else {
                puts("N");
                la = ty;
            }
        }
    }
    // cerr<<clock()/1000.<<endl;
    return 0;
}