/* ____  ______________  ________________________  __________
 * \   \/   /      \   \/   /   __/   /      \   \/   /      \
 *  \______/___/\___\______/___/_____/___/\___\______/___/\___\
 *
 * The MIT License (MIT)
 *
 * Copyright 2023 Vavr, https://vavr.io
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

import io.vavr.PartialFunction;
import io.vavr.Tuple;
import io.vavr.Tuple2;
import io.vavr.Tuple3;
import io.vavr.collection.Iterator;
import io.vavr.collection.Map;
import io.vavr.collection.Set;
import io.vavr.control.Option;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Spliterator;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collector;

/**
 * Implements an immutable set using a Compressed Hash-Array Mapped Prefix-tree
 * (CHAMP).
 * <p>
 * Features:
 * <ul>
 *     <li>supports up to 2<sup>30</sup> entries</li>
 *     <li>allows null elements</li>
 *     <li>is immutable</li>
 *     <li>is thread-safe</li>
 *     <li>does not guarantee a specific iteration order</li>
 * </ul>
 * <p>
 * Performance characteristics:
 * <ul>
 *     <li>add: O(1)</li>
 *     <li>remove: O(1)</li>
 *     <li>contains: O(1)</li>
 *     <li>toMutable: O(1) + O(log N) distributed across subsequent updates in the mutable copy</li>
 *     <li>clone: O(1)</li>
 *     <li>iterator.next(): O(1)</li>
 * </ul>
 * <p>
 * Implementation details:
 * <p>
 * This set performs read and write operations of single elements in O(1) time,
 * and in O(1) space.
 * <p>
 * The CHAMP trie contains nodes that may be shared with other sets.
 * <p>
 * If a write operation is performed on a node, then this set creates a
 * copy of the node and of all parent nodes up to the root (copy-path-on-write).
 * Since the CHAMP trie has a fixed maximal height, the cost is O(1).
 * <p>
 * The immutable version of this set extends from the non-public class
 * {@code ChampBitmapIndexNode}. This design safes 16 bytes for every instance,
 * and reduces the number of redirections for finding an element in the
 * collection by 1.
 * <p>
 * References:
 * <p>
 * Portions of the code in this class have been derived from 'The Capsule Hash Trie Collections Library', and from
 * 'JHotDraw 8'.
 * <dl>
 *     <dt>Michael J. Steindorfer (2017).
 *     Efficient Immutable Collections.</dt>
 *     <dd><a href="https://michael.steindorfer.name/publications/phd-thesis-efficient-immutable-collections">michael.steindorfer.name</a>
 *     </dd>
 *     <dt>The Capsule Hash Trie Collections Library.
 *     <br>Copyright (c) Michael Steindorfer. <a href="https://github.com/usethesource/capsule/blob/3856cd65fa4735c94bcfa94ec9ecf408429b54f4/LICENSE">BSD-2-Clause License</a></dt>
 *     <dd><a href="https://github.com/usethesource/capsule">github.com</a>
 *     </dd>
 *     <dt>JHotDraw 8. Copyright © 2023 The authors and contributors of JHotDraw.
 *     <a href="https://github.com/wrandelshofer/jhotdraw8/blob/8c1a98b70bc23a0c63f1886334d5b568ada36944/LICENSE">MIT License</a>.</dt>
 *     <dd><a href="https://github.com/wrandelshofer/jhotdraw8">github.com</a>
 *     </dd>
 * </dl>
 *
 * @param <T> the element type
 */
@SuppressWarnings("deprecation")
public final class ChampSet<T> implements Set<T>, Serializable {

    /**
     * We do not guarantee an iteration order. Make sure that nobody accidentally relies on it.
     * <p>
     * XXX HashSetTest requires a specific iteration order of ChampSet! Therefore, we can not use SALT here.
     */
    static final int SALT = 0;//new Random().nextInt();
    private static final long serialVersionUID = 1L;
    private static final ChampSet<?> EMPTY = new ChampSet<>(ChampTrie.BitmapIndexedNode.emptyNode(), 0);
    /**
     * The size of the set.
     */
    final int size;
    private final ChampTrie.BitmapIndexedNode<T> root;

    ChampSet(ChampTrie.BitmapIndexedNode<T> root, int size) {
        this.root = root;
        this.size = size;
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link ChampSet}.
     *
     * @param <T> Component type of the ChampSet.
     * @return A io.vavr.collection.ChampSet Collector.
     */
    public static <T> Collector<T, ArrayList<T>, ChampSet<T>> collector() {
        return Collections.toListAndThen(ChampSet::ofAll);
    }

    @SuppressWarnings("unchecked")
    public static <T> ChampSet<T> empty() {
        return (ChampSet<T>) EMPTY;
    }

    /**
     * Returns a ChampSet containing tuples returned by {@code n} calls to a given Supplier {@code s}.
     *
     * @param <T> Component type of the ChampSet
     * @param n   The number of elements in the ChampSet
     * @param s   The Supplier computing element values
     * @return An ChampSet of size {@code n}, where each element contains the result supplied by {@code s}.
     * @throws NullPointerException if {@code s} is null
     */
    public static <T> ChampSet<T> fill(int n, Supplier<? extends T> s) {
        Objects.requireNonNull(s, "s is null");
        return Collections.fill(n, s, ChampSet.empty(), ChampSet::of);
    }

    static int keyHash(Object e) {
        return SALT ^ Objects.hashCode(e);
    }

    /**
     * Narrows a widened {@code ChampSet<? extends T>} to {@code ChampSet<T>}
     * by performing a type-safe cast. This is eligible because immutable/read-only
     * collections are covariant.
     *
     * @param hashSet A {@code ChampSet}.
     * @param <T>     Component type of the {@code ChampSet}.
     * @return the given {@code hashSet} instance as narrowed type {@code ChampSet<T>}.
     */
    @SuppressWarnings("unchecked")
    public static <T> ChampSet<T> narrow(ChampSet<? extends T> hashSet) {
        return (ChampSet<T>) hashSet;
    }

    /**
     * Returns a singleton {@code ChampSet}, i.e. a {@code ChampSet} of one element.
     *
     * @param element An element.
     * @param <T>     The component type
     * @return A new ChampSet instance containing the given element
     */
    public static <T> ChampSet<T> of(T element) {
        return ChampSet.<T>empty().add(element);
    }

    /**
     * Creates a ChampSet of the given elements.
     *
     * <pre><code>ChampSet.of(1, 2, 3, 4)</code></pre>
     *
     * @param <T>      Component type of the ChampSet.
     * @param elements Zero or more elements.
     * @return A set containing the given elements.
     * @throws NullPointerException if {@code elements} is null
     */
    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <T> ChampSet<T> of(T... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.<T>empty().addAll(Arrays.asList(elements));
    }

    /**
     * Creates a ChampSet of the given elements.
     *
     * @param elements Set elements
     * @param <T>      The value type
     * @return A new ChampSet containing the given entries
     */
    @SuppressWarnings("unchecked")
    public static <T> ChampSet<T> ofAll(Iterable<? extends T> elements) {
        Objects.requireNonNull(elements, "elements is null");
        return elements instanceof ChampSet ? (ChampSet<T>) elements : ChampSet.<T>of().addAll(elements);
    }

    /**
     * Creates a ChampSet that contains the elements of the given {@link java.util.stream.Stream}.
     *
     * @param javaStream A {@link java.util.stream.Stream}
     * @param <T>        Component type of the Stream.
     * @return A ChampSet containing the given elements in the same order.
     */
    public static <T> ChampSet<T> ofAll(java.util.stream.Stream<? extends T> javaStream) {
        Objects.requireNonNull(javaStream, "javaStream is null");
        return ChampSet.ofAll(Iterator.ofAll(javaStream.iterator()));
    }

    /**
     * Creates a ChampSet from boolean values.
     *
     * @param elements boolean values
     * @return A new ChampSet of Boolean values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Boolean> ofAll(boolean... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet from byte values.
     *
     * @param elements byte values
     * @return A new ChampSet of Byte values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Byte> ofAll(byte... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet from char values.
     *
     * @param elements char values
     * @return A new ChampSet of Character values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Character> ofAll(char... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet from double values.
     *
     * @param elements double values
     * @return A new ChampSet of Double values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Double> ofAll(double... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet from float values.
     *
     * @param elements float values
     * @return A new ChampSet of Float values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Float> ofAll(float... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet from int values.
     *
     * @param elements int values
     * @return A new ChampSet of Integer values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Integer> ofAll(int... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet from long values.
     *
     * @param elements long values
     * @return A new ChampSet of Long values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Long> ofAll(long... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet from short values.
     *
     * @param elements short values
     * @return A new ChampSet of Short values
     * @throws NullPointerException if elements is null
     */
    public static ChampSet<Short> ofAll(short... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampSet of int numbers starting from {@code from}, extending to {@code toExclusive - 1}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.range(0, 0)  // = ChampSet()
     * ChampSet.range(2, 0)  // = ChampSet()
     * ChampSet.range(-2, 2) // = ChampSet(-2, -1, 0, 1)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toExclusive the last number + 1
     * @return a range of int values as specified or the empty range if {@code from >= toExclusive}
     */
    public static ChampSet<Integer> range(int from, int toExclusive) {
        return ChampSet.ofAll(Iterator.range(from, toExclusive));
    }

    public static ChampSet<Character> range(char from, char toExclusive) {
        return ChampSet.ofAll(Iterator.range(from, toExclusive));
    }

    /**
     * Creates a ChampSet of long numbers starting from {@code from}, extending to {@code toExclusive - 1}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.range(0L, 0L)  // = ChampSet()
     * ChampSet.range(2L, 0L)  // = ChampSet()
     * ChampSet.range(-2L, 2L) // = ChampSet(-2L, -1L, 0L, 1L)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toExclusive the last number + 1
     * @return a range of long values as specified or the empty range if {@code from >= toExclusive}
     */
    public static ChampSet<Long> range(long from, long toExclusive) {
        return ChampSet.ofAll(Iterator.range(from, toExclusive));
    }

    /**
     * Creates a ChampSet of int numbers starting from {@code from}, extending to {@code toExclusive - 1},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.rangeBy(1, 3, 1)  // = ChampSet(1, 2)
     * ChampSet.rangeBy(1, 4, 2)  // = ChampSet(1, 3)
     * ChampSet.rangeBy(4, 1, -2) // = ChampSet(4, 2)
     * ChampSet.rangeBy(4, 1, 2)  // = ChampSet()
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toExclusive the last number + 1
     * @param step        the step
     * @return a range of long values as specified or the empty range if<br>
     * {@code from >= toInclusive} and {@code step > 0} or<br>
     * {@code from <= toInclusive} and {@code step < 0}
     * @throws IllegalArgumentException if {@code step} is zero
     */
    public static ChampSet<Integer> rangeBy(int from, int toExclusive, int step) {
        return ChampSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    public static ChampSet<Character> rangeBy(char from, char toExclusive, int step) {
        return ChampSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    public static ChampSet<Double> rangeBy(double from, double toExclusive, double step) {
        return ChampSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    /**
     * Creates a ChampSet of long numbers starting from {@code from}, extending to {@code toExclusive - 1},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.rangeBy(1L, 3L, 1L)  // = ChampSet(1L, 2L)
     * ChampSet.rangeBy(1L, 4L, 2L)  // = ChampSet(1L, 3L)
     * ChampSet.rangeBy(4L, 1L, -2L) // = ChampSet(4L, 2L)
     * ChampSet.rangeBy(4L, 1L, 2L)  // = ChampSet()
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toExclusive the last number + 1
     * @param step        the step
     * @return a range of long values as specified or the empty range if<br>
     * {@code from >= toInclusive} and {@code step > 0} or<br>
     * {@code from <= toInclusive} and {@code step < 0}
     * @throws IllegalArgumentException if {@code step} is zero
     */
    public static ChampSet<Long> rangeBy(long from, long toExclusive, long step) {
        return ChampSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    /**
     * Creates a ChampSet of int numbers starting from {@code from}, extending to {@code toInclusive}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.rangeClosed(0, 0)  // = ChampSet(0)
     * ChampSet.rangeClosed(2, 0)  // = ChampSet()
     * ChampSet.rangeClosed(-2, 2) // = ChampSet(-2, -1, 0, 1, 2)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toInclusive the last number
     * @return a range of int values as specified or the empty range if {@code from > toInclusive}
     */
    public static ChampSet<Integer> rangeClosed(int from, int toInclusive) {
        return ChampSet.ofAll(Iterator.rangeClosed(from, toInclusive));
    }

    public static ChampSet<Character> rangeClosed(char from, char toInclusive) {
        return ChampSet.ofAll(Iterator.rangeClosed(from, toInclusive));
    }

    /**
     * Creates a ChampSet of long numbers starting from {@code from}, extending to {@code toInclusive}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.rangeClosed(0L, 0L)  // = ChampSet(0L)
     * ChampSet.rangeClosed(2L, 0L)  // = ChampSet()
     * ChampSet.rangeClosed(-2L, 2L) // = ChampSet(-2L, -1L, 0L, 1L, 2L)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toInclusive the last number
     * @return a range of long values as specified or the empty range if {@code from > toInclusive}
     */
    public static ChampSet<Long> rangeClosed(long from, long toInclusive) {
        return ChampSet.ofAll(Iterator.rangeClosed(from, toInclusive));
    }

    /**
     * Creates a ChampSet of int numbers starting from {@code from}, extending to {@code toInclusive},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.rangeClosedBy(1, 3, 1)  // = ChampSet(1, 2, 3)
     * ChampSet.rangeClosedBy(1, 4, 2)  // = ChampSet(1, 3)
     * ChampSet.rangeClosedBy(4, 1, -2) // = ChampSet(4, 2)
     * ChampSet.rangeClosedBy(4, 1, 2)  // = ChampSet()
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toInclusive the last number
     * @param step        the step
     * @return a range of int values as specified or the empty range if<br>
     * {@code from > toInclusive} and {@code step > 0} or<br>
     * {@code from < toInclusive} and {@code step < 0}
     * @throws IllegalArgumentException if {@code step} is zero
     */
    public static ChampSet<Integer> rangeClosedBy(int from, int toInclusive, int step) {
        return ChampSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    public static ChampSet<Character> rangeClosedBy(char from, char toInclusive, int step) {
        return ChampSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    public static ChampSet<Double> rangeClosedBy(double from, double toInclusive, double step) {
        return ChampSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    /**
     * Creates a ChampSet of long numbers starting from {@code from}, extending to {@code toInclusive},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampSet.rangeClosedBy(1L, 3L, 1L)  // = ChampSet(1L, 2L, 3L)
     * ChampSet.rangeClosedBy(1L, 4L, 2L)  // = ChampSet(1L, 3L)
     * ChampSet.rangeClosedBy(4L, 1L, -2L) // = ChampSet(4L, 2L)
     * ChampSet.rangeClosedBy(4L, 1L, 2L)  // = ChampSet()
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toInclusive the last number
     * @param step        the step
     * @return a range of int values as specified or the empty range if<br>
     * {@code from > toInclusive} and {@code step > 0} or<br>
     * {@code from < toInclusive} and {@code step < 0}
     * @throws IllegalArgumentException if {@code step} is zero
     */
    public static ChampSet<Long> rangeClosedBy(long from, long toInclusive, long step) {
        return ChampSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    /**
     * Returns an ChampSet containing {@code n} values of a given Function {@code f}
     * over a range of integer values from 0 to {@code n - 1}.
     *
     * @param <T> Component type of the ChampSet
     * @param n   The number of elements in the ChampSet
     * @param f   The Function computing element values
     * @return An ChampSet consisting of elements {@code f(0),f(1), ..., f(n - 1)}
     * @throws NullPointerException if {@code f} is null
     */
    public static <T> ChampSet<T> tabulate(int n, Function<? super Integer, ? extends T> f) {
        Objects.requireNonNull(f, "f is null");
        return Collections.tabulate(n, f, ChampSet.empty(), ChampSet::of);
    }

    /**
     * Update function for a set: we always keep the old element.
     *
     * @param oldElement the old element
     * @param newElement the new element
     * @param <E>        the element type
     * @return always returns the old element
     */
    static <E> E updateElement(E oldElement, E newElement) {
        return oldElement;
    }

    @Override
    public ChampSet<T> add(T element) {
        int keyHash = keyHash(element);
        ChampTrie.ChangeEvent<T> details = new ChampTrie.ChangeEvent<>();
        ChampTrie.BitmapIndexedNode<T> newRootNode = root.put(null, element, keyHash, 0, details, ChampSet::updateElement, Objects::equals, ChampSet::keyHash);
        if (details.isModified()) {
            return new ChampSet<>(newRootNode, size + 1);
        }
        return this;
    }

    @SuppressWarnings("unchecked")
    @Override
    public ChampSet<T> addAll(Iterable<? extends T> elements) {
        if (isEmpty() && elements instanceof ChampSet) {
            return (ChampSet<T>) elements;
        }
        TransientHashSet<T> t = toTransient();
        t.addAll(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public <R> ChampSet<R> collect(PartialFunction<? super T, ? extends R> partialFunction) {
        return ofAll(iterator().<R>collect(partialFunction));
    }

    @Override
    public boolean contains(T element) {
        return root.find(element, keyHash(element), 0, Objects::equals) != ChampTrie.Node.NO_DATA;
    }

    @Override
    public ChampSet<T> diff(Set<? extends T> elements) {
        Objects.requireNonNull(elements, "elements is null");
        if (isEmpty() || elements.isEmpty()) {
            return this;
        } else {
            return removeAll(elements);
        }
    }

    @Override
    public ChampSet<T> distinct() {
        return this;
    }

    @Override
    public ChampSet<T> distinctBy(Comparator<? super T> comparator) {
        Objects.requireNonNull(comparator, "comparator is null");
        return ChampSet.ofAll(iterator().distinctBy(comparator));
    }

    @Override
    public <U> ChampSet<T> distinctBy(Function<? super T, ? extends U> keyExtractor) {
        Objects.requireNonNull(keyExtractor, "keyExtractor is null");
        return ChampSet.ofAll(iterator().distinctBy(keyExtractor));
    }

    @Override
    public ChampSet<T> drop(int n) {
        if (n <= 0) {
            return this;
        } else {
            return ChampSet.ofAll(iterator().drop(n));
        }
    }

    @Override
    public ChampSet<T> dropRight(int n) {
        return drop(n);
    }

    @Override
    public ChampSet<T> dropUntil(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return dropWhile(predicate.negate());
    }

    @Override
    public ChampSet<T> dropWhile(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        final ChampSet<T> dropped = ChampSet.ofAll(iterator().dropWhile(predicate));
        return dropped.length() == length() ? this : dropped;
    }

    @Override
    public boolean equals(Object o) {
        return Collections.equals(this, o);
    }

    @Override
    public ChampSet<T> filter(Predicate<? super T> predicate) {
        TransientHashSet<T> t = toTransient();
        t.filterAll(predicate);
        return t.root == this.root ? this : t.toImmutable();
    }

    //@Override
    public ChampSet<T> filterNot(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return filter(predicate.negate());
    }

    @Override
    public <U> ChampSet<U> flatMap(Function<? super T, ? extends Iterable<? extends U>> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        if (isEmpty()) {
            return empty();
        } else {
            return foldLeft(ChampSet.empty(),
                    (tree, t) -> tree.addAll(mapper.apply(t)));
        }
    }

    @Override
    public <U> U foldRight(U zero, BiFunction<? super T, ? super U, ? extends U> f) {
        return foldLeft(zero, (u, t) -> f.apply(t, u));
    }

    @Override
    public <C> Map<C, ChampSet<T>> groupBy(Function<? super T, ? extends C> classifier) {
        return Collections.groupBy(this, classifier, ChampSet::ofAll);
    }

    @Override
    public Iterator<ChampSet<T>> grouped(int size) {
        return sliding(size, size);
    }

    @Override
    public boolean hasDefiniteSize() {
        return true;
    }

    @Override
    public int hashCode() {
        return Collections.hashUnordered(this);
    }

    @Override
    public T head() {
        if (isEmpty()) {
            throw new NoSuchElementException("head of empty set");
        }
        return ChampTrie.Node.getFirst(root);
    }

    @Override
    public Option<T> headOption() {
        return iterator().headOption();
    }

    @Override
    public ChampSet<T> init() {
        //XXX I would like to remove the last element here, but this would break HashSetTest.shouldGetInitOfNonNil().
        //if (isEmpty()) {
        //    throw new UnsupportedOperationException("init of empty set");
        //}
        //return remove(last());
        return tail();
    }

    @Override
    public Option<ChampSet<T>> initOption() {
        return tailOption();
    }

    @Override
    public ChampSet<T> intersect(Set<? extends T> elements) {
        return retainAll(elements);
    }

    /**
     * A {@code ChampSet} is computed synchronously.
     *
     * @return false
     */
    @Override
    public boolean isAsync() {
        return false;
    }

    @Override
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * A {@code ChampSet} is computed eagerly.
     *
     * @return false
     */
    @Override
    public boolean isLazy() {
        return false;
    }

    @Override
    public boolean isTraversableAgain() {
        return true;
    }

    @Override
    public Iterator<T> iterator() {
        return new ChampIteration.IteratorFacade<>(spliterator());
    }

    @Override
    public T last() {
        return ChampTrie.Node.getLast(root);
    }

    @Override
    public int length() {
        return size;
    }

    @Override
    public <U> ChampSet<U> map(Function<? super T, ? extends U> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        if (isEmpty()) {
            return empty();
        } else {
            return foldLeft(ChampSet.empty(),
                    (tree, t) -> {
                        final U u = mapper.apply(t);
                        return tree.add(u);
                    });
        }
    }

    @Override
    public String mkString(CharSequence prefix, CharSequence delimiter, CharSequence suffix) {
        return iterator().mkString(prefix, delimiter, suffix);
    }

    @Override
    public ChampSet<T> orElse(Iterable<? extends T> other) {
        return isEmpty() ? ofAll(other) : this;
    }

    @Override
    public ChampSet<T> orElse(Supplier<? extends Iterable<? extends T>> supplier) {
        return isEmpty() ? ofAll(supplier.get()) : this;
    }

    @Override
    public Tuple2<ChampSet<T>, ChampSet<T>> partition(Predicate<? super T> predicate) {
        //XXX HashSetTest#shouldPartitionInOneIteration prevents that we can use a faster implementation
        //XXX HashSetTest#partitionShouldBeUnique prevents that we can use a faster implementation
        //XXX I believe that these tests are wrong, because predicates should not have side effects!
        //return new Tuple2<>(filter(predicate),filter(predicate.negate()));
        return Collections.partition(this, ChampSet::ofAll, predicate);
    }

    @Override
    public ChampSet<T> peek(Consumer<? super T> action) {
        Objects.requireNonNull(action, "action is null");
        if (!isEmpty()) {
            action.accept(iterator().head());
        }
        return this;
    }

    /**
     * {@code readObject} method for the serialization proxy pattern.
     * <p>
     * Guarantees that the serialization system will never generate a serialized instance of the enclosing class.
     *
     * @param stream An object serialization stream.
     * @throws InvalidObjectException This method will throw with the message "Proxy required".
     */
    private void readObject(ObjectInputStream stream) throws InvalidObjectException {
        throw new InvalidObjectException("Proxy required");
    }

    @Override
    public ChampSet<T> reject(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.filter(predicate.negate());
    }

    @Override
    public ChampSet<T> remove(T key) {
        int keyHash = keyHash(key);
        ChampTrie.ChangeEvent<T> details = new ChampTrie.ChangeEvent<>();
        ChampTrie.BitmapIndexedNode<T> newRootNode = root.remove(null, key, keyHash, 0, details, Objects::equals);
        if (details.isModified()) {
            return size == 1 ? ChampSet.empty() : new ChampSet<>(newRootNode, size - 1);
        }
        return this;
    }

    @Override
    public ChampSet<T> removeAll(Iterable<? extends T> elements) {
        TransientHashSet<T> t = toTransient();
        t.removeAll(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public ChampSet<T> replace(T currentElement, T newElement) {
        ChampSet<T> removed = remove(currentElement);
        return removed != this ? removed.add(newElement) : this;
    }

    @Override
    public ChampSet<T> replaceAll(T currentElement, T newElement) {
        return replace(currentElement, newElement);
    }

    @Override
    public ChampSet<T> retainAll(Iterable<? extends T> elements) {
        TransientHashSet<T> t = toTransient();
        t.retainAll(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public ChampSet<T> scan(T zero, BiFunction<? super T, ? super T, ? extends T> operation) {
        return scanLeft(zero, operation);
    }

    @Override
    public <U> ChampSet<U> scanLeft(U zero, BiFunction<? super U, ? super T, ? extends U> operation) {
        return Collections.scanLeft(this, zero, operation, ChampSet::ofAll);
    }

    @Override
    public <U> ChampSet<U> scanRight(U zero, BiFunction<? super T, ? super U, ? extends U> operation) {
        return Collections.scanRight(this, zero, operation, ChampSet::ofAll);
    }

    @Override
    public Iterator<ChampSet<T>> slideBy(Function<? super T, ?> classifier) {
        return iterator().slideBy(classifier).map(ChampSet::ofAll);
    }

    @Override
    public Iterator<ChampSet<T>> sliding(int size) {
        return sliding(size, 1);
    }

    @Override
    public Iterator<ChampSet<T>> sliding(int size, int step) {
        return iterator().sliding(size, step).map(ChampSet::ofAll);
    }

    @Override
    public Tuple2<ChampSet<T>, ChampSet<T>> span(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        final Tuple2<Iterator<T>, Iterator<T>> t = iterator().span(predicate);
        return Tuple.of(ChampSet.ofAll(t._1), ChampSet.ofAll(t._2));
    }

    @Override
    public Spliterator<T> spliterator() {
        return new ChampIteration.ChampSpliterator<>(root, Function.identity(),
                Spliterator.DISTINCT | Spliterator.SIZED | Spliterator.SUBSIZED | Spliterator.IMMUTABLE, size);
    }

    @Override
    public String stringPrefix() {
        return "ChampSet";
    }

    @Override
    public ChampSet<T> tail() {
        if (isEmpty()) {
            throw new UnsupportedOperationException("tail of empty set");
        }
        return remove(head());
    }

    @Override
    public Option<ChampSet<T>> tailOption() {
        return isEmpty() ? Option.none() : Option.some(tail());
    }

    @Override
    public ChampSet<T> take(int n) {
        if (n >= size() || isEmpty()) {
            return this;
        } else if (n <= 0) {
            return empty();
        } else {
            return ofAll(() -> iterator().take(n));
        }
    }

    @Override
    public ChampSet<T> takeRight(int n) {
        return take(n);
    }

    @Override
    public ChampSet<T> takeUntil(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return takeWhile(predicate.negate());
    }

    @Override
    public ChampSet<T> takeWhile(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        final ChampSet<T> taken = ChampSet.ofAll(iterator().takeWhile(predicate));
        return taken.length() == length() ? this : taken;
    }

    @Override
    public java.util.HashSet<T> toJavaSet() {
        // XXX If the return value was not required to be a java.util.ChampSet
        //     we could provide a mutable ChampSet in O(1)
        return toJavaSet(java.util.HashSet::new);
    }

    @Override
    public String toString() {
        return mkString(stringPrefix() + "(", ", ", ")");
    }

    TransientHashSet<T> toTransient() {
        return new TransientHashSet<>(this);
    }

    /**
     * Transforms this {@code ChampSet}.
     *
     * @param f   A transformation
     * @param <U> Type of transformation result
     * @return An instance of type {@code U}
     * @throws NullPointerException if {@code f} is null
     */
    public <U> U transform(Function<? super ChampSet<T>, ? extends U> f) {
        Objects.requireNonNull(f, "f is null");
        return f.apply(this);
    }

    @SuppressWarnings("unchecked")
    @Override
    public ChampSet<T> union(Set<? extends T> elements) {
        return addAll(elements);
    }

    public <T1, T2> Tuple2<Iterator<T1>, Iterator<T2>> unzip(
            Function<? super T, ? extends T1> unzipper1, Function<? super T, ? extends T2> unzipper2) {
        Objects.requireNonNull(unzipper1, "unzipper1 is null");
        Objects.requireNonNull(unzipper2, "unzipper2 is null");
        final Iterator<T1> iter1 = iterator().map(unzipper1);
        final Iterator<T2> iter2 = iterator().map(unzipper2);
        return Tuple.of(iter1, iter2);
    }

    public <T1, T2> Tuple2<ChampSet<T1>, ChampSet<T2>> unzip(Function<? super T, Tuple2<? extends T1, ? extends T2>> unzipper) {
        Objects.requireNonNull(unzipper, "unzipper is null");
        Tuple2<Iterator<T1>, Iterator<T2>> t = this.iterator().unzip(unzipper);
        return Tuple.of(ofAll((Iterable) t._1), ofAll((Iterable) t._2));
    }

    public <T1, T2, T3> Tuple3<ChampSet<T1>, ChampSet<T2>, ChampSet<T3>> unzip3(Function<? super T, Tuple3<? extends T1, ? extends T2, ? extends T3>> unzipper) {
        Objects.requireNonNull(unzipper, "unzipper is null");
        Tuple3<Iterator<T1>, Iterator<T2>, Iterator<T3>> t = this.iterator().unzip3(unzipper);
        return Tuple.of(ofAll((Iterable) t._1), ofAll((Iterable) t._2), ofAll((Iterable) t._3));
    }

    // -- Object

    /**
     * {@code writeReplace} method for the serialization proxy pattern.
     * <p>
     * The presence of this method causes the serialization system to emit a SerializationProxy instance instead of
     * an instance of the enclosing class.
     *
     * @return A SerializationProxy for this enclosing class.
     */
    private Object writeReplace() {
        return new SerializationProxy<>(this);
    }

    @Override
    public <U> ChampSet<Tuple2<T, U>> zip(Iterable<? extends U> that) {
        return zipWith(that, Tuple::of);
    }

    @Override
    public <U> ChampSet<Tuple2<T, U>> zipAll(Iterable<? extends U> that, T thisElem, U thatElem) {
        Objects.requireNonNull(that, "that is null");
        return ChampSet.ofAll(iterator().zipAll(that, thisElem, thatElem));
    }

    @Override
    public <U, R> ChampSet<R> zipWith(Iterable<? extends U> that, BiFunction<? super T, ? super U, ? extends R> mapper) {
        Objects.requireNonNull(that, "that is null");
        Objects.requireNonNull(mapper, "mapper is null");
        return ChampSet.ofAll(iterator().zipWith(that, mapper));
    }


    // -- Serialization

    @Override
    public ChampSet<Tuple2<T, Integer>> zipWithIndex() {
        return zipWithIndex(Tuple::of);
    }

    @Override
    public <U> ChampSet<U> zipWithIndex(BiFunction<? super T, ? super Integer, ? extends U> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        return ChampSet.ofAll(iterator().zipWithIndex(mapper));
    }

    /**
     * A serialization proxy which, in this context, is used to deserialize immutable, linked Lists with final
     * instance fields.
     *
     * @param <T> The component type of the underlying list.
     */
    // DEV NOTE: The serialization proxy pattern is not compatible with non-final, i.e. extendable,
    // classes. Also, it may not be compatible with circular object graphs.
    private static final class SerializationProxy<T> implements Serializable {

        private static final long serialVersionUID = 1L;

        // the instance to be serialized/deserialized
        private transient ChampSet<T> tree;

        /**
         * Constructor for the case of serialization, called by {@link ChampSet#writeReplace()}.
         * <p/>
         * The constructor of a SerializationProxy takes an argument that concisely represents the logical state of
         * an instance of the enclosing class.
         *
         * @param tree a Cons
         */
        SerializationProxy(ChampSet<T> tree) {
            this.tree = tree;
        }

        /**
         * Read an object from a deserialization stream.
         *
         * @param s An object deserialization stream.
         * @throws ClassNotFoundException If the object's class read from the stream cannot be found.
         * @throws InvalidObjectException If the stream contains no list elements.
         * @throws IOException            If an error occurs reading from the stream.
         */
        private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
            s.defaultReadObject();
            final int size = s.readInt();
            if (size < 0) {
                throw new InvalidObjectException("No elements");
            }
            ChampTrie.IdentityObject owner = new ChampTrie.IdentityObject();
            ChampTrie.BitmapIndexedNode<T> newRoot = ChampTrie.BitmapIndexedNode.emptyNode();
            ChampTrie.ChangeEvent<T> details = new ChampTrie.ChangeEvent<>();
            int newSize = 0;
            for (int i = 0; i < size; i++) {
                @SuppressWarnings("unchecked") final T element = (T) s.readObject();
                int keyHash = keyHash(element);
                newRoot = newRoot.put(owner, element, keyHash, 0, details, ChampSet::updateElement, Objects::equals, ChampSet::keyHash);
                if (details.isModified()) newSize++;
            }
            tree = newSize == 0 ? empty() : new ChampSet<>(newRoot, newSize);
        }

        /**
         * {@code readResolve} method for the serialization proxy pattern.
         * <p>
         * Returns a logically equivalent instance of the enclosing class. The presence of this method causes the
         * serialization system to translate the serialization proxy back into an instance of the enclosing class
         * upon deserialization.
         *
         * @return A deserialized instance of the enclosing class.
         */
        private Object readResolve() {
            return tree;
        }

        /**
         * Write an object to a serialization stream.
         *
         * @param s An object serialization stream.
         * @throws IOException If an error occurs writing to the stream.
         */
        private void writeObject(ObjectOutputStream s) throws IOException {
            s.defaultWriteObject();
            s.writeInt(tree.size());
            for (T e : tree) {
                s.writeObject(e);
            }
        }
    }

    /**
     * Supports efficient bulk-operations on a set through transience.
     *
     * @param <E>the element type
     */
    static class TransientHashSet<E> extends ChampTransience.ChampAbstractTransientSet<E, E> {
        TransientHashSet(ChampSet<E> s) {
            root = s.root;
            size = s.size;
        }

        TransientHashSet() {
            this(empty());
        }

        boolean add(E e) {
            ChampTrie.ChangeEvent<E> details = new ChampTrie.ChangeEvent<>();
            root = root.put(makeOwner(),
                    e, keyHash(e), 0, details,
                    (oldKey, newKey) -> oldKey,
                    Objects::equals, ChampSet::keyHash);
            if (details.isModified()) {
                size++;
                modCount++;
            }
            return details.isModified();
        }

        @SuppressWarnings("unchecked")
        boolean addAll(Iterable<? extends E> c) {
            if (c == root) {
                return false;
            }
            if (isEmpty() && (c instanceof ChampSet<?>)) {
                ChampSet<?> cc = (ChampSet<?>) c;
                root = (ChampTrie.BitmapIndexedNode<E>) cc.root;
                size = cc.size;
                return true;
            }
            if (c instanceof ChampSet<?>) {
                ChampSet<?> that = (ChampSet<?>) c;
                ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
                ChampTrie.BitmapIndexedNode<E> newRootNode = root.putAll(makeOwner(), (ChampTrie.Node<E>) that.root, 0, bulkChange, ChampSet::updateElement, Objects::equals, ChampSet::keyHash, new ChampTrie.ChangeEvent<>());
                if (bulkChange.inBoth == that.size()) {
                    return false;
                }
                root = newRootNode;
                size += that.size - bulkChange.inBoth;
                modCount++;
                return true;
            }
            boolean added = false;
            for (E e : c) {
                added |= add(e);
            }
            return added;
        }

        void clear() {
            root = ChampTrie.BitmapIndexedNode.emptyNode();
            size = 0;
            modCount++;
        }

        public boolean filterAll(Predicate<? super E> predicate) {
            ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
            ChampTrie.BitmapIndexedNode<E> newRootNode
                    = root.filterAll(makeOwner(), predicate, 0, bulkChange);
            if (bulkChange.removed == 0) {
                return false;
            }
            root = newRootNode;
            size -= bulkChange.removed;
            modCount++;
            return true;

        }

        @Override
        public java.util.Iterator<E> iterator() {
            return new ChampIteration.IteratorFacade<>(spliterator());
        }

        @SuppressWarnings("unchecked")
        @Override
        boolean remove(Object key) {
            int keyHash = keyHash(key);
            ChampTrie.ChangeEvent<E> details = new ChampTrie.ChangeEvent<>();
            root = root.remove(owner, (E) key, keyHash, 0, details, Objects::equals);
            if (details.isModified()) {
                size--;
                return true;
            }
            return false;
        }

        @SuppressWarnings("unchecked")
        boolean removeAll(Iterable<?> c) {
            if (isEmpty()
                    || (c instanceof Collection<?>) && ((Collection<?>) c).isEmpty()) {
                return false;
            }
            if (c instanceof ChampSet<?>) {
                ChampSet<?> that = (ChampSet<?>) c;
                ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
                ChampTrie.BitmapIndexedNode<E> newRootNode = root.removeAll(makeOwner(), (ChampTrie.BitmapIndexedNode<E>) that.root, 0, bulkChange, ChampSet::updateElement, Objects::equals, ChampSet::keyHash, new ChampTrie.ChangeEvent<>());
                if (bulkChange.removed == 0) {
                    return false;
                }
                root = newRootNode;
                size -= bulkChange.removed;
                modCount++;
                return true;
            }
            return super.removeAll(c);
        }

        @SuppressWarnings("unchecked")
        boolean retainAll(Iterable<?> c) {
            if (isEmpty()) {
                return false;
            }
            if ((c instanceof Collection<?> && ((Collection<?>) c).isEmpty())) {
                Collection<?> cc = (Collection<?>) c;
                clear();
                return true;
            }
            ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
            ChampTrie.BitmapIndexedNode<E> newRootNode;
            if (c instanceof ChampSet<?>) {
                ChampSet<?> that = (ChampSet<?>) c;
                newRootNode = root.retainAll(makeOwner(), (ChampTrie.BitmapIndexedNode<E>) that.root, 0, bulkChange, ChampSet::updateElement, Objects::equals, ChampSet::keyHash, new ChampTrie.ChangeEvent<>());
            } else if (c instanceof Collection<?>) {
                Collection<?> that = (Collection<?>) c;
                newRootNode = root.filterAll(makeOwner(), that::contains, 0, bulkChange);
            } else {
                java.util.HashSet<Object> that = new java.util.HashSet<>();
                c.forEach(that::add);
                newRootNode = root.filterAll(makeOwner(), that::contains, 0, bulkChange);
            }
            if (bulkChange.removed == 0) {
                return false;
            }
            root = newRootNode;
            size -= bulkChange.removed;
            modCount++;
            return true;
        }

        public Spliterator<E> spliterator() {
            return new ChampIteration.ChampSpliterator<>(root, Function.identity(), Spliterator.DISTINCT | Spliterator.SIZED, size);
        }

        public ChampSet<E> toImmutable() {
            owner = null;
            return isEmpty()
                    ? empty()
                    : new ChampSet<>(root, size);
        }
    }
}
