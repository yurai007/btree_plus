#include <array>
#include <vector>
#include <cassert>
#include <stdexcept>
#include <variant>
#include <cstdio>
#include <algorithm>
#include <string>

constexpr auto debug = true;
constexpr auto artificial_fanout = 8u;

template<class Key = unsigned, class Data = unsigned>
class btree_plus {
public:
    btree_plus() : root(allocate_page(false)) {
        write(*root);
    }
    btree_plus(const btree_plus&) noexcept = delete;
    btree_plus& operator=(const btree_plus&) noexcept = delete;

    const Data *search(const Key &key) const noexcept {
        return do_search(root, key);
    }

    void insert(const Key &key, const Data &data) {
        auto r = root;
        if (r->empty()) {
            auto new_child = allocate_page(true);
            r->set_external(0, key, new_child);
            do_insert(new_child, key, data);
        } else if (r->full()) {
            auto new_root = allocate_page(false);
            root->leaf = true;
            root = new_root;
            split_child(new_root, 1u, r);
            do_insert(new_root, key, data);
        } else {
            do_insert(r, key, data);
        }
    }

    void dump() const {
        if (!debug)
            return;
        do_dump(root, "");
    }

    ~btree_plus() {
        do_delete(root);
    }

private:
    struct page;
    using internal_page = page*;
    using external_page_offset = unsigned;
    using page_ptr = std::variant<internal_page, external_page_offset>;

    struct cell {
        Key key;
        std::variant<Data, page_ptr> value;
    };

    struct page_header {
        uint32_t magic = 0xDEAD;
        page_ptr next_sibling = nullptr;
        uint32_t cells_size = 0, availibility_list_size = 0;
    };

    using cell_ptr = cell*;

    constexpr static auto page_size = 4'096u;
    constexpr static auto payload_size = page_size - sizeof(page_header);
    constexpr static auto offsets_capacity = static_cast<unsigned>(0.25f*(payload_size))/sizeof(cell_ptr);
    constexpr static auto cells_capacity = static_cast<unsigned>(0.5f*(payload_size))/sizeof(cell);
    constexpr static auto availibility_list_capacity = static_cast<unsigned>(0.5f*(payload_size))/sizeof(cell_ptr);

    struct page {
        page_header header;
        // [ cell pointers | [free space] | cells ]
        std::array<cell_ptr, offsets_capacity> offsets;
        std::array<cell, cells_capacity> cells;
        std::array<cell_ptr, availibility_list_capacity> availibility_list;
        bool leaf;

        bool full() const noexcept {
            return fanout == header.cells_size;
        }

        bool empty() const noexcept {
            return size() == 0;
        }

        bool is_leaf() const noexcept {
            return leaf;
        }

        page_ptr get_child(unsigned i) const {
            auto &data = offsets;
            return std::get<page_ptr>(data[i]->value);
        }

        external_page_offset get_external_child(unsigned i) const {
            return std::get<external_page_offset>(get_child(i));
        }

        internal_page get_internal_child(unsigned i) const {
            return std::get<internal_page>(get_child(i));
        }

        Data *get_data(unsigned i) noexcept {
            auto &data = offsets;
            return std::get_if<Data>(&data[i]->value);
        }

        void set_internal(unsigned i, const Key &key, const Data &data) {
            offsets[i] = &cells[header.cells_size++];
            offsets[i]->key = key;
            offsets[i]->value = data;
        }

        void set_external(unsigned i, const Key &key, const internal_page page_) {
            offsets[i] = &cells[header.cells_size++];
            offsets[i]->key = key;
            offsets[i]->value = page_;
        }

        void set(unsigned i, const Key &key, const std::variant<Data, page_ptr> &value) {
            offsets[i] = &cells[header.cells_size++];
            offsets[i]->key = key;
            offsets[i]->value = value;
        }

        unsigned size() const noexcept {
            return header.cells_size;
        }
    };

    page *root;
    unsigned short binary_search_threshold = fanout/2;
    unsigned short memory_limit_mb = 512u;

    const Data *do_search(page *node, const Key &key) const noexcept {
        if (debug)
            printf("do_search: %u\n", key);
        auto size = node->size();
        auto &data = node->offsets;
        // data are sorted
        if (size < binary_search_threshold) [[likely]] {
            // for now just naive scan
            auto i = 0u;
            for (; (i < size) && (key > data[i]->key); i++) {}
            if (i < size) {
                assert(key <= data[i]->key);
                if (node->is_leaf() && data[i]->key == key) {
                     return node->get_data(i);
                } else if (!node->is_leaf() && !node->empty()) {
                    auto next_page = read(node->get_internal_child(i));
                    return next_page? do_search(next_page, key) : nullptr;
                }
            }
            return nullptr;
        } else {
            auto it = std::ranges::lower_bound(data.begin(), data.begin() + size, key, [](auto key1, auto key2){
                return key1 < key2;
            }, [](auto cell_pointer){
                return cell_pointer->key;
            });
            assert(it != data.end());
            auto i = std::ranges::distance(data.begin(), it);
            if (data[i]->key == key) {
                return node->get_data(i);
            } else {
                auto next_page = read(node->get_internal_child(i));
                return next_page? do_search(next_page, key) : nullptr;
            }
        }
    }

    void do_insert(page *node, const Key &key, const Data &value) {
        if (debug)
            printf("do_insert: %u\n", key);
        auto &data = node->offsets;
        auto i = node->size();
        if (node->is_leaf()) {
            for (; (i >= 1u) && (key < data[i-1]->key); i--) {
                data[i] = data[i-1];
            }
            node->set_internal(i, key, value);
            write(*node);
        } else {
            for (; (i >= 1u) && (key < data[i-1]->key); i--) {}
            if (i == node->size())
                i--;
            auto next_page = read(node->get_internal_child(i));
            auto splitted = next_page->full();
            if (splitted) {
                auto new_page = split_child(node, i, next_page);
                if (key > data[i]->key) {
                    next_page = new_page;
                    i++;
                }
            }
            do_insert(next_page, key, value);
            if (!splitted)
                data[i]->key = std::max(data[i]->key, key);
        }
    }
    // x - parent of full y, right half of y is moved to z - new child of x
    page* split_child(page *x, unsigned i, page *y) {
        if (debug)
            printf("split_child index: %u\n", i);

        auto z = allocate_page(y->is_leaf());
        auto half = fanout/2u;
        z->header.cells_size = 0;
        auto &x_data = x->offsets;
        auto &z_data = z->offsets;
        auto &y_data = y->offsets;

        for (auto j = 0u; j < half; j++) {
            auto ptr = y_data[j + half];
            z->set(j, ptr->key, ptr->value);
        }
        // no need to remove upper half from list
        y->header.cells_size = half;
        for (auto j = x->header.cells_size; j >= i + 1; j--) {
            x_data[j+1] = x_data[j];
        }
        x->set(i+1, z_data[half - 1]->key, z);
        x_data[i]->key = y_data[half - 1]->key;
        write(*x);
        write(*y);
        write(*z);
        return z;
    }

    void do_dump(page *node, std::string str) const {
        using namespace std::string_literals;
        printf("%s %p: leaf = %d\n", str.c_str(), (void*)node, node->is_leaf());
        str += "  "s;
        for (auto i = 0u; i < node->size(); i++) {
            auto &data = node->offsets;
            printf("%s key = %u\n", str.c_str(), data[i]->key);
            if (!node->is_leaf())
                do_dump(node->get_internal_child(i), str);
        }
    }

    void do_delete(page *node) {
        for (auto i = 0u; i < node->size(); i++) {
            if (!node->is_leaf())
                do_delete(node->get_internal_child(i));
        }
        delete node;
    }

    page *allocate_page(bool leaf) {
        auto new_page = new page;
        new_page->leaf = leaf;
        return new_page;
    }

    static page *read(external_page_offset offset) {
        // page may be already in memory, do fseek
        if (debug)
            printf("read: not implemented yet\n");
        return nullptr;
    }

    static page *read(internal_page page) {
        return page;
    }

    static void write(const page &p) {
        if (debug)
            printf("write: not implemented yet\n");
    }
public:
    constexpr static auto fanout = debug? artificial_fanout : std::min(offsets_capacity,
                                          std::min(cells_capacity, availibility_list_capacity));
};

static_assert(btree_plus<unsigned, unsigned>::fanout == 63u ||
    btree_plus<unsigned, unsigned>::fanout == artificial_fanout);
// static_asserts + trivially_copyable + standard_layut + no padding stuff (concepts?)

static auto test_basic_insert_search1() {
    printf("%s\n", __PRETTY_FUNCTION__);
    btree_plus<unsigned, std::string> tree;
    assert(tree.search(1) == nullptr);
    tree.insert(1, "1");
    assert(*tree.search(1) == "1");
    tree.insert(2, "2");
    tree.insert(3, "3");
    assert(*tree.search(2) == "2");
    assert(tree.search(0) == nullptr);
    tree.dump();
}

static auto test_basic_insert_search2() {
    printf("%s\n", __PRETTY_FUNCTION__);
    btree_plus<unsigned, std::string> tree;
    assert(tree.search(1) == nullptr);
    tree.insert(2, "2");
    tree.insert(5, "5");
    assert(*tree.search(2) == "2");
    assert(tree.search(3) == nullptr);
    tree.dump();
    tree.insert(3, "3");
    assert(*tree.search(3) == "3");
    tree.insert(1, "1");
    assert(*tree.search(1) == "1");
    tree.insert(6, "6");
    tree.insert(0, "0");
    tree.insert(4, "4");
    for (auto i = 0u; i < 7u; i++)
        assert(tree.search(i));
    assert(tree.search(7) == nullptr);
    tree.dump();
}

static auto test_basic_insert_search3() {
    printf("%s\n", __PRETTY_FUNCTION__);
    btree_plus<unsigned, std::string> tree;
    assert(tree.search(3) == nullptr);
    tree.insert(3, "3");
    assert(*tree.search(3) == "3");
    tree.insert(2, "2");
    tree.insert(1, "1");
    assert(*tree.search(2) == "2");
    assert(tree.search(0) == nullptr);
    tree.dump();
}

// provokes split_child
static auto test_inserts_with_full_leaf() {
    printf("%s\n", __PRETTY_FUNCTION__);
    btree_plus<unsigned, std::string> tree;
    for (auto i = 0u; i < 32u; i++) {
        tree.insert(i, std::to_string(i));
    }
    tree.dump();
}

int main() {
    test_basic_insert_search1();
    test_basic_insert_search2();
    test_basic_insert_search3();
    test_inserts_with_full_leaf();
    printf("OK\n");
    return 0;
}
