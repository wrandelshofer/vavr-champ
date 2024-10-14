/* ____  ______________  ________________________  __________
 * \   \/   /      \   \/   /   __/   /      \   \/   /      \
 *  \______/___/\___\______/___/_____/___/\___\______/___/\___\
 *
 * The MIT License (MIT)
 *
 * Copyright 2024 Vavr, https://vavr.io
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package ch.randelshofer.vavr.champ;


import io.vavr.collection.Iterator;

import java.io.Serializable;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Spliterators;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;

import static ch.randelshofer.vavr.champ.ArrayType.obj;
import static ch.randelshofer.vavr.champ.ChampTrie.ChampListHelper.checkIndex;
import static ch.randelshofer.vavr.champ.Collections.withSize;
import static java.util.function.Function.identity;

@FunctionalInterface
interface NodeModifier {
    NodeModifier COPY_NODE = (o, i) -> obj().copy(o, i + 1);
    NodeModifier IDENTITY = (o, i) -> o;

    Object apply(Object array, int index);
}

@FunctionalInterface
interface LeafVisitor<T> {
    int visit(int index, T leaf, int start, int end);
}

/**
 * A `bit-mapped trie` is a very wide and shallow tree (for integer indices the depth will be `≤6`).
 * Each node has a maximum of `32` children (configurable).
 * Access to a given position is done by converting the index to a base 32 number and using each digit to descend down the tree.
 * Modifying the tree is done similarly, but along the way the path is copied, returning a new root every time.
 * `Append` inserts in the last leaf, or if the tree is full from the right, it adds another layer on top of it (the old root will be the first of the new one).
 * `Prepend` is done similarly, but an offset is needed, because adding a new top node (where the current root would be the last node of the new root)
 * shifts the indices by half of the current tree's full size. The `offset` shifts them back to the correct index.
 * `Slice` is done by trimming the path from the root and discarding any `leading`/`trailing` values in effectively constant time (without memory leak, as in `Java`/`Clojure`).
 */
final class BitMappedTrie<T> implements Serializable {

    static final int BRANCHING_BASE = 5;
    static final int BRANCHING_FACTOR = 1 << BRANCHING_BASE;
    static final int BRANCHING_MASK = -1 >>> -BRANCHING_BASE;
    private static final long serialVersionUID = 1L;
    private static final BitMappedTrie<?> EMPTY = new BitMappedTrie<>(obj(), obj().empty(), 0, 0, 0);
    final ArrayType<T> type;
    @SuppressWarnings("serial") // Conditionally serializable
    private final Object array;
    private final int offset, length;
    private final int depthShift;

    private BitMappedTrie(ArrayType<T> type, Object array, int offset, int length, int depthShift) {
        this.type = type;
        this.array = array;
        this.offset = offset;
        this.length = length;
        this.depthShift = depthShift;
    }

    /* drop root node while it has a single element */
    private static <T> BitMappedTrie<T> collapsed(ArrayType<T> type, Object array, int offset, int length, int shift) {
        for (; shift > 0; shift -= BRANCHING_BASE) {
            final int skippedElements = obj().lengthOf(array) - 1;
            if (skippedElements != digit(offset, shift)) {
                break;
            }
            array = obj().getAt(array, skippedElements);
            offset -= treeSize(skippedElements, shift);
        }
        return new BitMappedTrie<>(type, array, offset, length, shift);
    }

    static int digit(int num, int depthShift) {
        return lastDigit(firstDigit(num, depthShift));
    }

    @SuppressWarnings("unchecked")
    static <T> BitMappedTrie<T> empty() {
        return (BitMappedTrie<T>) EMPTY;
    }

    static int firstDigit(int num, int depthShift) {
        return num >> depthShift;
    }

    static int lastDigit(int num) {
        return num & BRANCHING_MASK;
    }

    static <T> BitMappedTrie<T> of(T element) {
        return ofAll(BitMappedTrie.ofAll(new Object[]{element}));
    }

    static <T> BitMappedTrie<T> of(T... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return elements.length == 0 ? empty() : ofAll(BitMappedTrie.ofAll(elements));
    }

    static <T> BitMappedTrie<T> ofAll(Iterable<? extends T> iterable) {
        Objects.requireNonNull(iterable, "iterable is null");
        final Object[] values = withSize(iterable).toArray();
        return ofAll(BitMappedTrie.ofAll(values));
    }

    static <T> BitMappedTrie<T> ofAll(Object array) {
        final ArrayType<T> type = ArrayType.of(array);
        final int size = type.lengthOf(array);
        return (size == 0) ? empty() : ofAll(array, type, size);
    }

    private static <T> BitMappedTrie<T> ofAll(Object array, ArrayType<T> type, int size) {
        int shift = 0;
        for (ArrayType<T> t = type; t.lengthOf(array) > BRANCHING_FACTOR; shift += BRANCHING_BASE) {
            array = t.grouped(array, BRANCHING_FACTOR);
            t = obj();
        }
        return new BitMappedTrie<>(type, array, 0, size, shift);
    }

    private static int treeSize(int branchCount, int depthShift) {
        final int fullBranchSize = 1 << depthShift;
        return branchCount * fullBranchSize;
    }

    BitMappedTrie<T> append(T element) {
        return appendAll(io.vavr.collection.List.of(element));
    }

    private BitMappedTrie<T> append(java.util.Iterator<? extends T> iterator, int size) {
        BitMappedTrie<T> result = this;
        while (size > 0) {
            Object array = result.array;
            int shift = result.depthShift;
            if (result.isFullRight()) {
                array = obj().asArray(array);
                shift += BRANCHING_BASE;
            }

            final int index = offset + result.length;
            final int leafSpace = lastDigit(index);
            final int delta = Math.min(size, BRANCHING_FACTOR - leafSpace);
            size -= delta;

            array = result.modify(array, shift, index, NodeModifier.COPY_NODE, appendToLeaf(iterator, leafSpace + delta));
            result = new BitMappedTrie<>(type, array, offset, result.length + delta, shift);
        }
        return result;

    }

    BitMappedTrie<T> appendAll(Iterable<? extends T> iterable) {
        final Collections.IterableWithSize<? extends T> iter = withSize(iterable);
        try {
            return append(iter.iterator(), iter.size());
        } catch (ClassCastException ignored) {
            return boxed().append(iter.iterator(), iter.size());
        }
    }

    private NodeModifier appendToLeaf(java.util.Iterator<? extends T> iterator, int leafSize) {
        return (array, index) -> {
            final Object copy = type.copy(array, leafSize);
            while (iterator.hasNext() && index < leafSize) {
                type.setAt(copy, index++, iterator.next());
            }
            return copy;
        };
    }

    T apply(Integer index) {
        return get(index);
    }

    private boolean arePointingToSameLeaf(int i, int j) {
        return firstDigit(offset + i, BRANCHING_BASE) == firstDigit(offset + j, BRANCHING_BASE);
    }

    private BitMappedTrie<T> boxed() {
        return map(identity());
    }

    BitMappedTrie<T> drop(int n) {
        if (n <= 0) {
            return this;
        } else if (n >= length) {
            return empty();
        } else {
            final int index = offset + n;
            final Object root = arePointingToSameLeaf(0, n)
                    ? array
                    : modify(array, depthShift, index, obj()::copyDrop, NodeModifier.IDENTITY);
            return collapsed(type, root, index, length - n, depthShift);
        }
    }

    BitMappedTrie<T> dropRight(int n) {
        return take(length() - n);
    }

    BitMappedTrie<T> filter(Predicate<? super T> predicate) {
        final Object results = type.newInstance(length());
        final int length = this.<T>visit((index, leaf, start, end) -> filter(predicate, results, index, leaf, start, end));
        return (this.length == length)
                ? this
                : BitMappedTrie.ofAll(type.copyRange(results, 0, length));
    }

    private int filter(Predicate<? super T> predicate, Object results, int index, T leaf, int start, int end) {
        for (int i = start; i < end; i++) {
            final T value = type.getAt(leaf, i);
            if (predicate.test(value)) {
                type.setAt(results, index++, value);
            }
        }
        return index;
    }


    //--------END

    T get(int index) {
        final Object leaf = getLeaf(index);
        final int leafIndex = lastDigit(offset + index);
        return type.getAt(leaf, leafIndex);
    }

    /**
     * fetch the leaf, corresponding to the given index.
     * Node: the offset and length should be taken into consideration as there may be leading and trailing garbage.
     * Also, the returned array is mutable, but should not be mutated!
     */
    @SuppressWarnings("WeakerAccess")
    Object getLeaf(int index) {
        if (depthShift == 0) {
            return array;
        } else {
            return getLeafGeneral(index);
        }
    }

    private Object getLeafGeneral(int index) {
        index += offset;
        Object leaf = obj().getAt(array, firstDigit(index, depthShift));
        for (int shift = depthShift - BRANCHING_BASE; shift > 0; shift -= BRANCHING_BASE) {
            leaf = obj().getAt(leaf, digit(index, shift));
        }
        return leaf;
    }

    private int getMin(int start, int index, Object leaf) {
        return Math.min(type.lengthOf(leaf), start + length - index);
    }

    T head() {
        if (nonEmpty()) {
            return get(0);
        } else {
            throw new NoSuchElementException("head of empty BitMappedTrie");
        }
    }

    BitMappedTrie<T> init() {
        if (nonEmpty()) {
            return dropRight(1);
        } else {
            throw new UnsupportedOperationException("init of empty BitMappedTrie");
        }
    }

    //--------BEGIN
    boolean isDefinedAt(Integer index) {
        return 0 <= index && index < length();
    }

    boolean isEmpty() {
        return length() == 0;
    }

    private boolean isFullLeft() {
        return offset == 0;
    }

    private boolean isFullRight() {
        return (offset + length + 1) > treeSize(BRANCHING_FACTOR, depthShift);
    }

    Iterator<T> iterator(int index) {
        return subSequence(index).iterator();
    }

    io.vavr.collection.Iterator<T> iterator() {
        return new io.vavr.collection.Iterator<T>() {
            private final int globalLength = BitMappedTrie.this.length;
            private int globalIndex = 0;

            private int index = lastDigit(offset);
            private Object leaf = getLeaf(globalIndex);
            private int length = type.lengthOf(leaf);

            @Override
            public boolean hasNext() {
                return globalIndex < globalLength;
            }

            @Override
            public T next() {
                if (!hasNext()) {
                    throw new NoSuchElementException("next() on empty iterator");
                }

                if (index == length) {
                    setCurrentArray();
                }
                final T next = type.getAt(leaf, index);

                index++;
                globalIndex++;

                return next;
            }

            private void setCurrentArray() {
                index = 0;
                leaf = getLeaf(globalIndex);
                length = type.lengthOf(leaf);
            }
        };
    }

    T last() {
        if (isEmpty()) {
            throw new NoSuchElementException("last of empty IndexedSeq");
        } else {
            return get(length() - 1);
        }
    }

    int length() {
        return length;
    }

    <U> BitMappedTrie<U> map(Function<? super T, ? extends U> mapper) {
        final Object results = obj().newInstance(length);
        this.<T>visit((index, leaf, start, end) -> map(mapper, results, index, leaf, start, end));
        return BitMappedTrie.ofAll(results);
    }

    private <U> int map(Function<? super T, ? extends U> mapper, Object results, int index, T leaf, int start, int end) {
        for (int i = start; i < end; i++) {
            obj().setAt(results, index++, mapper.apply(type.getAt(leaf, i)));
        }
        return index;
    }

    /* descend the tree from root to leaf, applying the given modifications along the way, returning the new root */
    private Object modify(Object root, int depthShift, int index, NodeModifier node, NodeModifier leaf) {
        return (depthShift == 0)
                ? leaf.apply(root, index)
                : modifyNonLeaf(root, depthShift, index, node, leaf);
    }

    private Object modifyNonLeaf(Object root, int depthShift, int index, NodeModifier node, NodeModifier leaf) {
        int previousIndex = firstDigit(index, depthShift);
        root = node.apply(root, previousIndex);

        Object array = root;
        for (int shift = depthShift - BRANCHING_BASE; shift >= BRANCHING_BASE; shift -= BRANCHING_BASE) {
            final int prev = previousIndex;
            previousIndex = digit(index, shift);
            array = setNewNode(node, prev, array, previousIndex);
        }

        final Object newLeaf = leaf.apply(obj().getAt(array, previousIndex), lastDigit(index));
        obj().setAt(array, previousIndex, newLeaf);
        return root;
    }

    boolean nonEmpty() {
        return !isEmpty();
    }

    private BitMappedTrie<T> prepend(java.util.Iterator<? extends T> iterator, int size) {
        BitMappedTrie<T> result = this;
        while (size > 0) {
            Object array = result.array;
            int shift = result.depthShift, offset = result.offset;
            if (result.isFullLeft()) {
                array = obj().copyUpdate(obj().empty(), BRANCHING_FACTOR - 1, array);
                shift += BRANCHING_BASE;
                offset = treeSize(BRANCHING_FACTOR - 1, shift);
            }

            final int index = offset - 1;
            final int delta = Math.min(size, lastDigit(index) + 1);
            size -= delta;

            array = result.modify(array, shift, index, NodeModifier.COPY_NODE, prependToLeaf(iterator));
            result = new BitMappedTrie<>(type, array, offset - delta, result.length + delta, shift);
        }
        return result;
    }

    BitMappedTrie<T> prependAll(Iterable<? extends T> iterable) {
        final Collections.IterableWithSize<? extends T> iter = withSize(iterable);
        try {
            return prepend(iter.reverseIterator(), iter.size());
        } catch (ClassCastException ignored) {
            return boxed().prepend(iter.reverseIterator(), iter.size());
        }
    }

    private NodeModifier prependToLeaf(java.util.Iterator<? extends T> iterator) {
        return (array, index) -> {
            final Object copy = type.copy(array, BRANCHING_FACTOR);
            while (iterator.hasNext() && index >= 0) {
                type.setAt(copy, index--, iterator.next());
            }
            return copy;
        };
    }

    BitMappedTrie<T> removeRange(int fromIndex, int toIndex) {
        int size = size();
        checkIndex(fromIndex, toIndex + 1);
        checkIndex(toIndex, size + 1);
        if (fromIndex == 0) {
            return slice(toIndex, size);
        }
        if (toIndex == size) {
            return slice(0, fromIndex);
        }
        final BitMappedTrie<T> begin = slice(0, fromIndex);
        return begin.appendAll(() -> slice(toIndex, size).iterator());
    }

    private Object setNewNode(NodeModifier node, int previousIndex, Object array, int offset) {
        final Object previous = obj().getAt(array, previousIndex);
        final Object newNode = node.apply(previous, offset);
        obj().setAt(array, previousIndex, newNode);
        return newNode;
    }

    int size() {
        return length();
    }

    BitMappedTrie<T> slice(int beginIndex, int endIndex) {
        if ((beginIndex >= endIndex) || (beginIndex >= size()) || isEmpty()) {
            return empty();
        } else if ((beginIndex <= 0) && (endIndex >= length())) {
            return this;
        } else {
            return take(endIndex).drop(beginIndex);
        }
    }

    BitMappedTrie<T> subSequence(int beginIndex) {
        if ((beginIndex >= 0) && (beginIndex <= length())) {
            return drop(beginIndex);
        } else {
            throw new IndexOutOfBoundsException("subSequence(" + beginIndex + ")");
        }
    }

    BitMappedTrie<T> tail() {
        if (nonEmpty()) {
            return drop(1);
        } else {
            throw new UnsupportedOperationException("tail of empty BitMappedTrie");
        }
    }

    BitMappedTrie<T> take(int n) {
        if (n >= length) {
            return this;
        } else if (n <= 0) {
            return empty();
        } else {
            final int index = n - 1;
            final Object root = arePointingToSameLeaf(index, length - 1)
                    ? array
                    : modify(array, depthShift, offset + index, obj()::copyTake, NodeModifier.IDENTITY);
            return collapsed(type, root, offset, n, depthShift);
        }
    }

    BitMappedTrie<T> update(int index, T element) {
        try {
            final Object root = modify(array, depthShift, offset + index, NodeModifier.COPY_NODE, updateLeafWith(type, element));
            return new BitMappedTrie<>(type, root, offset, length, depthShift);
        } catch (ClassCastException ignored) {
            return boxed().update(index, element);
        }
    }

    private NodeModifier updateLeafWith(ArrayType<T> type, T element) {
        return (a, i) -> type.copyUpdate(a, i, element);
    }

    @SuppressWarnings("unchecked")
    <T2> int visit(LeafVisitor<T2> visitor) {
        int globalIndex = 0, start = lastDigit(offset);
        for (int index = 0; index < length; ) {
            final T2 leaf = (T2) getLeaf(index);
            final int end = getMin(start, index, leaf);

            globalIndex = visitor.visit(globalIndex, leaf, start, end);

            index += end - start;
            start = 0;
        }
        return globalIndex;
    }

    static class BitMappedTrieSpliterator<T> extends Spliterators.AbstractSpliterator<T> {
        private final int globalLength;
        private final BitMappedTrie<T> root;
        private int globalIndex;
        private int index;
        private Object leaf;
        private int length;
        private T current;

        public BitMappedTrieSpliterator(BitMappedTrie<T> root, int fromIndex, int characteristics) {
            super(Math.max(0, root.length - fromIndex), characteristics);
            this.root = root;
            globalLength = root.length;
            globalIndex = Math.max(0, fromIndex);
            index = lastDigit(root.offset + globalIndex);
            leaf = root.getLeaf(globalIndex);
            length = root.type.lengthOf(leaf);
        }

        public T current() {
            return current;
        }

        public boolean moveNext() {
            if (globalIndex >= globalLength) {
                return false;
            }
            if (index == length) {
                setCurrentArray();
            }
            current = root.type.getAt(leaf, index);
            index++;
            globalIndex++;
            return true;
        }

        private void setCurrentArray() {
            index = 0;
            leaf = root.getLeaf(globalIndex);
            length = root.type.lengthOf(leaf);
        }

        public void skip(int count) {
            globalIndex += count;
            index = lastDigit(root.offset + globalIndex);
            leaf = root.getLeaf(globalIndex);
            length = root.type.lengthOf(leaf);
        }

        @Override
        public boolean tryAdvance(Consumer<? super T> action) {
            if (moveNext()) {
                action.accept(current);
                return true;
            }
            return false;
        }
    }
}
