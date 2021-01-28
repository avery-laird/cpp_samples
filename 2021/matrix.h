//
// Created by avery on 2021-01-16.
//

#ifndef SPARSE_MATRIX_OPT_MATRIX_H
#define SPARSE_MATRIX_OPT_MATRIX_H

#include <string>
#include <stdexcept>
#include <cmath>
#include "utils.h"

template<class ValueType>
class Vector {
public:
    explicit Vector(std::string path) {
        bool res = inputRHS(path, n, NNZ, m);
        if (!res) throw std::runtime_error("failed to read vector");
    }

    explicit Vector(int n) {
        m = new ValueType[n]();
    }

    Vector(const Vector<ValueType>& v) : n(v.n), NNZ(v.NNZ) {
        std::copy(v.m, v.m+v.n, m);
    }

    int n{};
    int NNZ{};
    ValueType *m;
};


template<class ValueType>
class SparseMatrix {
public:
    explicit SparseMatrix(std::string path) {
        bool res = inputMatrix(path, n, NNZ, col, row, m);
        if (!res) throw std::runtime_error("failed to read matrix");
    }

    int *row{}; // row index
    int *col{}; // column pointers
    int n;
    int NNZ;
    ValueType *m;
};


template<class ValueType>
bool operator==(Vector<ValueType> const &a, Vector<ValueType> const &b) {
    if (a.n != b.n) return false;
    for (int i = 0; i < a.n; i++) {
        if (a.m[i] == b.m[i] ||
            nearlyEqual(a.m[i], b.m[i]) ||
            (std::isnan(a.m[i]) || std::isinf(a.m[i])) && (std::isnan(b.m[i]) || std::isinf(b.m[i])))
            continue;
        else return false;
    }
    return true;
}

#endif //SPARSE_MATRIX_OPT_MATRIX_H
