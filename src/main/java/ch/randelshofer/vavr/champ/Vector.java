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

import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.function.Function;

import static ch.randelshofer.vavr.champ.ChampTrie.ChampListHelper.checkIndex;
import static ch.randelshofer.vavr.champ.Collections.withSize;

/**
 * Vector is the default Seq implementation that provides effectively constant time access to any element.
 * Many other operations (e.g. `tail`, `drop`, `slice`) are also effectively constant.
 * <p>
 * The implementation is based on a `bit-mapped trie`, a very wide and shallow tree (i.e. depth ≤ 6).
 *
 * @param <T> Component type of the Vector.
 */
class Vector<T> {


    private static final Vector<?> EMPTY = new Vector<>(BitMappedTrie.empty());

    final BitMappedTrie<T> trie;

    private Vector(BitMappedTrie<T> trie) {
        this.trie = trie;
    }

    boolean isDefinedAt(Integer index) {
        return 0 <= index && index < length();
    }

    Vector<T> slice(int beginIndex, int endIndex) {
        if ((beginIndex >= endIndex) || (beginIndex >= size()) || isEmpty()) {
            return empty();
        } else if ((beginIndex <= 0) && (endIndex >= length())) {
            return this;
        } else {
            return take(endIndex).drop(beginIndex);
        }
    }

    Vector<T> drop(int n) {
        return wrap(trie.drop(n));
    }

    Vector<T> removeRange(int fromIndex, int toIndex) {
        int size = size();
        checkIndex(fromIndex, toIndex + 1);
        checkIndex(toIndex, size + 1);
        if (fromIndex == 0) {
            return slice(toIndex, size);
        }
        if (toIndex == size) {
            return slice(0, fromIndex);
        }
        final Vector<T> begin = slice(0, fromIndex);
        return begin.appendAll(() -> slice(toIndex, size).iterator());
    }

    int length() {
        return trie.length();
    }

    T apply(Integer index) {
        return trie.get(index);
    }

    T get(int index) {
        if (isDefinedAt(index)) {
            return apply(index);
        }
        throw new IndexOutOfBoundsException("get(" + index + ")");
    }

    int size() {
        return length();
    }

    boolean isEmpty() {
        return length() == 0;
    }

    Vector<T> wrap(BitMappedTrie<T> trie) {
        return (trie == this.trie)
                ? this
                : ofAll(trie);
    }

    static <T> Vector<T> ofAll(BitMappedTrie<T> trie) {
        return (trie.length() == 0)
                ? empty()
                : new Vector<>(trie);
    }

    Vector<T> dropRight(int n) {
        return take(length() - n);
    }

    Vector<T> init() {
        if (nonEmpty()) {
            return dropRight(1);
        } else {
            throw new UnsupportedOperationException("init of empty Vector");
        }
    }

    Vector<T> update(int index, Function<? super T, ? extends T> updater) {
        Objects.requireNonNull(updater, "updater is null");
        return update(index, updater.apply(get(index)));
    }

    Vector<T> update(int index, T element) {
        if (isDefinedAt(index)) {
            return wrap(trie.update(index, element));
        } else {
            throw new IndexOutOfBoundsException("update(" + index + ")");
        }
    }

    Vector<T> tail() {
        if (nonEmpty()) {
            return drop(1);
        } else {
            throw new UnsupportedOperationException("tail of empty Vector");
        }
    }

    Vector<T> append(T element) {
        return appendAll(io.vavr.collection.List.of(element));
    }

    T head() {
        if (nonEmpty()) {
            return get(0);
        } else {
            throw new NoSuchElementException("head of empty Vector");
        }
    }

    T last() {
        if (isEmpty()) {
            throw new NoSuchElementException("last of empty IndexedSeq");
        } else {
            return get(length() - 1);
        }
    }
    boolean nonEmpty() {
        return !isEmpty();
    }

    static <T> Vector<T> of(T element) {
        return ofAll(BitMappedTrie.ofAll(new Object[]{element}));
    }
    static <T> Vector<T> of(T... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ofAll(BitMappedTrie.ofAll(elements));
    }
    static <T> Vector<T> empty() {
        return (Vector<T>) EMPTY;
    }

    Iterator<T> iterator(int index) {
        return subSequence(index).iterator();
    }

    Vector<T> take(int n) {
        return wrap(trie.take(n));
    }

    Vector<T> subSequence(int beginIndex) {
        if ((beginIndex >= 0) && (beginIndex <= length())) {
            return drop(beginIndex);
        } else {
            throw new IndexOutOfBoundsException("subSequence(" + beginIndex + ")");
        }
    }


    public Vector<T> subSequence(int beginIndex, int endIndex) {
        Collections.subSequenceRangeCheck(beginIndex, endIndex, length());
        return slice(beginIndex, endIndex);
    }

    static <T> Vector<T> ofAll(Iterable<? extends T> iterable) {
        Objects.requireNonNull(iterable, "iterable is null");
        final Object[] values = withSize(iterable).toArray();
        return ofAll(BitMappedTrie.ofAll(values));
    }

    Vector<T> appendAll(Iterable<? extends T> iterable) {
        Objects.requireNonNull(iterable, "iterable is null");
        if (isEmpty()) {
            return ofAll(iterable);
        }
        if (Collections.isEmpty(iterable)) {
            return this;
        }
        return new Vector<>(trie.appendAll(iterable));
    }

    Iterator<T> iterator() {
        return isEmpty() ? Iterator.empty()
                : trie.iterator();
    }
}
