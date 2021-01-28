//
// Created by avery on 2021-01-16.
//

#include <cmath>
#include <limits>
#include <set>
#include "utils.h"

// copied from program specification
/*
* Lower triangular solver Lx=b
* L is stored in the compressed column storage format
* Inputs are:
* n : the matrix dimension
* Lp : the column pointer of L
* Li : the row index of L
* Lx : the values of L
* In/Out:
* x : the right hand-side b at start and the solution x at the end.
*/
int lsolve(int n, int *Lp, int *Li, double *Lx, double *&x) {
    int p, j;
    if (!Lp || !Li || !x) return (0); /* check inputs */
    for (j = 0; j < n; j++) {
        x[j] /= Lx[Lp[j]];
        for (p = Lp[j] + 1; p < Lp[j + 1]; p++) {
            x[Li[p]] -= Lx[p] * x[j];
        }
    }
    return (1);
}



// https://floating-point-gui.de/errors/comparison/
bool nearlyEqual(float a, float b) {
    double absA = std::abs(a);
    double absB = std::abs(b);
    double diff = std::abs(a - b);

    if (a == b) { // shortcut, handles infinities
        return true;
    } else if (a == 0 || b == 0 || (absA + absB < std::numeric_limits<double>::min())) {
        // a or b is zero or both are extremely close to it
        // relative error is less meaningful here
        return diff < (std::numeric_limits<double>::min() * std::numeric_limits<double>::min());
    } else { // use relative error
        return diff / std::min((absA + absB), std::numeric_limits<double>::max()) < std::numeric_limits<double>::min();
    }
}


