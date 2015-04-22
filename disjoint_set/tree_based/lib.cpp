class Node {
    friend Node* Find_Set(Node*);
    
    int rank;
    Node* p;
    const void* item;
public:
    Node(const void* x) : rank(0), p(this), item(x) {}

    bool is_root() const {
        return p == this;
    }
    
    Node* link(Node* other) {
        if (rank > other->rank) {
            other->p = this;
            return this;
        } //rank <= other->rank

        p = other;
        if (rank == other->rank)
            other->rank += 1;
        return other;
    }
};

Node* Find_Set(Node* x) {
    Node* y = x->p;
    if (x == y)
        return x;
    return (x->p = Find_Set(y));
}

Node* Union(Node* x, Node* y) {
    return Find_Set(x)->link(Find_Set(y));
}


