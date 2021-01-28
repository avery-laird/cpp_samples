
// Begin instructor code
#include <cstdint>
#include <cstdio>
// End instructor code
#include <map>
#include <vector>
#include <iostream>

// Begin instructor code
extern "C" {

// This macro allows us to prefix strings so that they are less likely to
// conflict with existing symbol names in the examined programs.
// e.g. TOLERATE(entry) yields ToLeRaToR_entry
#define TOLERATE(X) ToLeRaToR_##X
// End instructor code


std::map<int64_t, int64_t > heap;
std::vector<std::map<int64_t, int64_t >> stack;
std::map<int64_t, int64_t >* _global_mem = nullptr;


void
TOLERATE(handle_alloca)(int64_t addr, int64_t size) {
    stack.back().insert({addr, size});
}

void
TOLERATE(handle_malloc)(int64_t addr, int64_t size) {
    heap.insert({addr, size});
}

bool
valid_memory_bounds(std::pair<int64_t, int64_t> pair, int64_t addr, int64_t size) {
    return pair.first <= addr && addr + size <= pair.first + pair.second;
}

std::pair<int64_t, int64_t>
find_closest_addr(std::map<int64_t, int64_t> map, int64_t addr) {
    auto closest = map.lower_bound(addr);
    if (closest == map.end())
        return std::pair<int64_t, int64_t>(-1, -1);
    else if ((*closest).first == addr)
        return *closest;
    else if (closest != map.begin())
        return *(--closest);
    return std::pair<int64_t, int64_t>(-1, -1);
}

bool
search_memory(int64_t addr, int64_t size, bool store) {
    std::vector<std::map<int64_t, int64_t>> to_check = {stack.back(), heap, *_global_mem};
    int bound = store ? to_check.size()-1 : to_check.size();
    for (int i = 0; i < bound; i++) {
        auto closest = find_closest_addr(to_check[i], addr);
        if (closest.first == -1) continue;
        if (valid_memory_bounds(closest, addr, size)) {
            return true;
        }
    }
    return false;
}

int64_t
TOLERATE(handle_store)(int64_t addr, int64_t size) {
    return (int64_t)search_memory(addr, size, true);
}


int64_t
TOLERATE(handle_load)(int64_t addr, int64_t size) {
    return (int64_t)search_memory(addr, size, false);
}

int64_t
TOLERATE(handle_free)(int64_t addr) {
    auto elem = heap.find(addr);
    if (elem == heap.end()) {
        printf("FOUND: Invalid free of memory\n");
        return 0;
    }
    heap.erase(elem);
    return 1;
}


int64_t
TOLERATE(handle_div)(int64_t denom) {
    if (denom == 0) {
        printf("FOUND: Division by zero\n");
        return 0;
    }
    return 1;
}

void
TOLERATE(handle_push)() {
    stack.push_back(std::map<int64_t,int64_t>());
}

void
TOLERATE(handle_pop)() {
    stack.erase(--stack.end());
}

void
TOLERATE(handle_global)(int64_t addr, int64_t size) {
    if (_global_mem == nullptr)
        _global_mem = new std::map<int64_t, int64_t>;
    _global_mem->insert({addr, size});
}

void
TOLERATE(init_global)() {
    if (_global_mem == nullptr)
        _global_mem = new std::map<int64_t, int64_t>;
}

}
