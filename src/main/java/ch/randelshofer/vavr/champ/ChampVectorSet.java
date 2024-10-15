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
import java.util.Comparator;
import java.util.Objects;
import java.util.Spliterator;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collector;

import static ch.randelshofer.vavr.champ.ChampSequenced.ChampSequencedData.vecRemove;
import static ch.randelshofer.vavr.champ.ChampTrie.BitmapIndexedNode.emptyNode;


/**
 * Implements a mutable set using a Compressed Hash-Array Mapped Prefix-tree
 * (CHAMP) and a bit-mapped trie (BitMappedTrie).
 * <p>
 * Features:
 * <ul>
 *     <li>supports up to 2<sup>30</sup> elements</li>
 *     <li>allows null elements</li>
 *     <li>is immutable</li>
 *     <li>is thread-safe</li>
 *     <li>iterates in the order, in which elements were inserted</li>
 * </ul>
 * <p>
 * Performance characteristics:
 * <ul>
 *     <li>add: O(log N) in an amortized sense, because we sometimes have to
 *     renumber the elements.</li>
 *     <li>remove: O(log N) in an amortized sense, because we sometimes have to
 *     renumber the elements.</li>
 *     <li>contains: O(1)</li>
 *     <li>toMutable: O(1) + O(log N) distributed across subsequent updates in
 *     the mutable copy</li>
 *     <li>clone: O(1)</li>
 *     <li>iterator creation: O(1)</li>
 *     <li>iterator.next: O(log N)</li>
 *     <li>getFirst(), getLast(): O(log N)</li>
 * </ul>
 * <p>
 * Implementation details:
 * <p>
 * This set performs read and write operations of single elements in O(log N) time,
 * and in O(log N) space, where N is the number of elements in the set.
 * <p>
 * The CHAMP trie contains nodes that may be shared with other sets.
 * <p>
 * If a write operation is performed on a node, then this set creates a
 * copy of the node and of all parent nodes up to the root (copy-path-on-write).
 * Since the CHAMP trie has a fixed maximal height, the cost is O(1).
 * <p>
 * Insertion Order:
 * <p>
 * This set uses a counter to keep track of the insertion order.
 * It stores the current value of the counter in the sequence number
 * field of each data entry. If the counter wraps around, it must renumber all
 * sequence numbers.
 * <p>
 * The renumbering is why the {@code add} and {@code remove} methods are O(1)
 * only in an amortized sense.
 * <p>
 * To support iteration, we use a BitMappedTrie. The BitMappedTrie has the same contents
 * as the CHAMP trie. However, its elements are stored in insertion order.
 * <p>
 * If an element is removed from the CHAMP trie that is not the first or the
 * last element of the BitMappedTrie, we replace its corresponding element in
 * the BitMappedTrie by a tombstone. If the element is at the start or end of the BitMappedTrie,
 * we remove the element and all its neighboring tombstones from the BitMappedTrie.
 * <p>
 * A tombstone can store the number of neighboring tombstones in ascending and in descending
 * direction. We use these numbers to skip tombstones when we iterate over the vector.
 * Since we only allow iteration in ascending or descending order from one of the ends of
 * the vector, we do not need to keep the number of neighbors in all tombstones up to date.
 * It is sufficient, if we update the neighbor with the lowest index and the one with the
 * highest index.
 * <p>
 * If the number of tombstones exceeds half of the size of the collection, we renumber all
 * sequence numbers, and we create a new BitMappedTrie.
 * <p>
 * The immutable version of this set extends from the non-public class
 * {@code ChampBitmapIndexNode}. This design safes 16 bytes for every instance,
 * and reduces the number of redirections for finding an element in the
 * collection by 1.
 * <p>
 * References:
 * <p>
 * Portions of the code in this class have been derived from JHotDraw8 'VectorSet.java'.
 * <p>
 * For a similar design, see 'VectorMap.scala'. Note, that this code is not a derivative
 * of that code.
 * <dl>
 *     <dt>JHotDraw 8. VectorSet.java. Copyright © 2023 The authors and contributors of JHotDraw.
 *     <a href="https://github.com/wrandelshofer/jhotdraw8/blob/8c1a98b70bc23a0c63f1886334d5b568ada36944/LICENSE">MIT License</a>.</dt>
 *     <dd><a href="https://github.com/wrandelshofer/jhotdraw8">github.com</a></dd>
 *     <dt>The Scala library. VectorMap.scala. Copyright EPFL and Lightbend, Inc. Apache License 2.0.</dt>
 *     <dd><a href="https://github.com/scala/scala/blob/28eef15f3cc46f6d3dd1884e94329d7601dc20ee/src/library/scala/collection/immutable/VectorMap.scala">github.com</a>
 *     </dd>
 * </dl>
 *
 * @param <T> the element type
 */
public class ChampVectorSet<T> implements Set<T>, Serializable {

    private static final long serialVersionUID = 1L;

    private static final ChampVectorSet<?> EMPTY = new ChampVectorSet<>(
            emptyNode(), BitMappedTrie.of(), 0, 0);
    /**
     * Offset of sequence numbers to vector indices.
     *
     * <pre>vector index = sequence number + offset</pre>
     */
    final int offset;
    /**
     * The size of the set.
     */
    final int size;
    /**
     * In this vector we store the elements in the order in which they were inserted.
     */
    final BitMappedTrie<Object> vector;
    private final ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<T>> root;

    ChampVectorSet(
            ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<T>> root,
            BitMappedTrie<Object> vector,
            int size, int offset) {
        this.root = root;
        this.size = size;
        this.offset = offset;
        this.vector = Objects.requireNonNull(vector);
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link ChampVectorSet}.
     *
     * @param <T> Component type of the ChampVectorSet.
     * @return A io.vavr.collection.ChampVectorSet Collector.
     */
    public static <T> Collector<T, ArrayList<T>, ChampVectorSet<T>> collector() {
        return Collections.toListAndThen(ChampVectorSet::ofAll);
    }

    @SuppressWarnings("unchecked")
    public static <T> ChampVectorSet<T> empty() {
        return (ChampVectorSet<T>) EMPTY;
    }

    /**
     * Returns a ChampVectorSet containing tuples returned by {@code n} calls to a given Supplier {@code s}.
     *
     * @param <T> Component type of the ChampVectorSet
     * @param n   The number of elements in the ChampVectorSet
     * @param s   The Supplier computing element values
     * @return A ChampVectorSet of size {@code n}, where each element contains the result supplied by {@code s}.
     * @throws NullPointerException if {@code s} is null
     */
    public static <T> ChampVectorSet<T> fill(int n, Supplier<? extends T> s) {
        Objects.requireNonNull(s, "s is null");
        return Collections.fill(n, s, ChampVectorSet.empty(), ChampVectorSet::of);
    }

    /**
     * Narrows a widened {@code ChampVectorSet<? extends T>} to {@code ChampVectorSet<T>}
     * by performing a type-safe cast. This is eligible because immutable/read-only
     * collections are covariant.
     *
     * @param linkedHashSet A {@code ChampVectorSet}.
     * @param <T>           Component type of the {@code linkedHashSet}.
     * @return the given {@code linkedHashSet} instance as narrowed type {@code ChampVectorSet<T>}.
     */
    @SuppressWarnings("unchecked")
    public static <T> ChampVectorSet<T> narrow(ChampVectorSet<? extends T> linkedHashSet) {
        return (ChampVectorSet<T>) linkedHashSet;
    }

    /**
     * Returns a singleton {@code ChampVectorSet}, i.e. a {@code ChampVectorSet} of one element.
     *
     * @param element An element.
     * @param <T>     The component type
     * @return A new ChampVectorSet instance containing the given element
     */
    public static <T> ChampVectorSet<T> of(T element) {
        return ChampVectorSet.<T>empty().add(element);
    }

    /**
     * Creates a ChampVectorSet of the given elements.
     *
     * <pre><code>ChampVectorSet.of(1, 2, 3, 4)</code></pre>
     *
     * @param <T>      Component type of the ChampVectorSet.
     * @param elements Zero or more elements.
     * @return A set containing the given elements.
     * @throws NullPointerException if {@code elements} is null
     */
    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <T> ChampVectorSet<T> of(T... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.<T>empty().addAll(Arrays.asList(elements));
    }

    /**
     * Creates a ChampVectorSet of the given elements.
     *
     * @param elements Set elements
     * @param <T>      The value type
     * @return A new ChampVectorSet containing the given entries
     */
    @SuppressWarnings("unchecked")
    public static <T> ChampVectorSet<T> ofAll(Iterable<? extends T> elements) {
        Objects.requireNonNull(elements, "elements is null");
        return elements instanceof ChampVectorSet ? (ChampVectorSet<T>) elements : ChampVectorSet.<T>of().addAll(elements);
    }

    /**
     * Creates a ChampVectorSet that contains the elements of the given {@link java.util.stream.Stream}.
     *
     * @param javaStream A {@link java.util.stream.Stream}
     * @param <T>        Component type of the Stream.
     * @return A ChampVectorSet containing the given elements in the same order.
     */
    public static <T> ChampVectorSet<T> ofAll(java.util.stream.Stream<? extends T> javaStream) {
        Objects.requireNonNull(javaStream, "javaStream is null");
        return ofAll(Iterator.ofAll(javaStream.iterator()));
    }

    /**
     * Creates a ChampVectorSet from boolean values.
     *
     * @param elements boolean values
     * @return A new ChampVectorSet of Boolean values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Boolean> ofAll(boolean... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet from byte values.
     *
     * @param elements byte values
     * @return A new ChampVectorSet of Byte values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Byte> ofAll(byte... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet from char values.
     *
     * @param elements char values
     * @return A new ChampVectorSet of Character values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Character> ofAll(char... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet from double values.
     *
     * @param elements double values
     * @return A new ChampVectorSet of Double values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Double> ofAll(double... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet from float values.
     *
     * @param elements a float values
     * @return A new ChampVectorSet of Float values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Float> ofAll(float... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet from int values.
     *
     * @param elements int values
     * @return A new ChampVectorSet of Integer values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Integer> ofAll(int... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet from long values.
     *
     * @param elements long values
     * @return A new ChampVectorSet of Long values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Long> ofAll(long... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet from short values.
     *
     * @param elements short values
     * @return A new ChampVectorSet of Short values
     * @throws NullPointerException if elements is null
     */
    public static ChampVectorSet<Short> ofAll(short... elements) {
        Objects.requireNonNull(elements, "elements is null");
        return ChampVectorSet.ofAll(Iterator.ofAll(elements));
    }

    /**
     * Creates a ChampVectorSet of int numbers starting from {@code from}, extending to {@code toExclusive - 1}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.range(0, 0)  // = ChampVectorSet()
     * ChampVectorSet.range(2, 0)  // = ChampVectorSet()
     * ChampVectorSet.range(-2, 2) // = ChampVectorSet(-2, -1, 0, 1)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toExclusive the last number + 1
     * @return a range of int values as specified or the empty range if {@code from >= toExclusive}
     */
    public static ChampVectorSet<Integer> range(int from, int toExclusive) {
        return ChampVectorSet.ofAll(Iterator.range(from, toExclusive));
    }

    public static ChampVectorSet<Character> range(char from, char toExclusive) {
        return ChampVectorSet.ofAll(Iterator.range(from, toExclusive));
    }

    /**
     * Creates a ChampVectorSet of long numbers starting from {@code from}, extending to {@code toExclusive - 1}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.range(0L, 0L)  // = ChampVectorSet()
     * ChampVectorSet.range(2L, 0L)  // = ChampVectorSet()
     * ChampVectorSet.range(-2L, 2L) // = ChampVectorSet(-2L, -1L, 0L, 1L)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toExclusive the last number + 1
     * @return a range of long values as specified or the empty range if {@code from >= toExclusive}
     */
    public static ChampVectorSet<Long> range(long from, long toExclusive) {
        return ChampVectorSet.ofAll(Iterator.range(from, toExclusive));
    }

    /**
     * Creates a ChampVectorSet of int numbers starting from {@code from}, extending to {@code toExclusive - 1},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.rangeBy(1, 3, 1)  // = ChampVectorSet(1, 2)
     * ChampVectorSet.rangeBy(1, 4, 2)  // = ChampVectorSet(1, 3)
     * ChampVectorSet.rangeBy(4, 1, -2) // = ChampVectorSet(4, 2)
     * ChampVectorSet.rangeBy(4, 1, 2)  // = ChampVectorSet()
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
    public static ChampVectorSet<Integer> rangeBy(int from, int toExclusive, int step) {
        return ChampVectorSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    public static ChampVectorSet<Character> rangeBy(char from, char toExclusive, int step) {
        return ChampVectorSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    public static ChampVectorSet<Double> rangeBy(double from, double toExclusive, double step) {
        return ChampVectorSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    /**
     * Creates a ChampVectorSet of long numbers starting from {@code from}, extending to {@code toExclusive - 1},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.rangeBy(1L, 3L, 1L)  // = ChampVectorSet(1L, 2L)
     * ChampVectorSet.rangeBy(1L, 4L, 2L)  // = ChampVectorSet(1L, 3L)
     * ChampVectorSet.rangeBy(4L, 1L, -2L) // = ChampVectorSet(4L, 2L)
     * ChampVectorSet.rangeBy(4L, 1L, 2L)  // = ChampVectorSet()
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
    public static ChampVectorSet<Long> rangeBy(long from, long toExclusive, long step) {
        return ChampVectorSet.ofAll(Iterator.rangeBy(from, toExclusive, step));
    }

    /**
     * Creates a ChampVectorSet of int numbers starting from {@code from}, extending to {@code toInclusive}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.rangeClosed(0, 0)  // = ChampVectorSet(0)
     * ChampVectorSet.rangeClosed(2, 0)  // = ChampVectorSet()
     * ChampVectorSet.rangeClosed(-2, 2) // = ChampVectorSet(-2, -1, 0, 1, 2)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toInclusive the last number
     * @return a range of int values as specified or the empty range if {@code from > toInclusive}
     */
    public static ChampVectorSet<Integer> rangeClosed(int from, int toInclusive) {
        return ChampVectorSet.ofAll(Iterator.rangeClosed(from, toInclusive));
    }

    public static ChampVectorSet<Character> rangeClosed(char from, char toInclusive) {
        return ChampVectorSet.ofAll(Iterator.rangeClosed(from, toInclusive));
    }

    /**
     * Creates a ChampVectorSet of long numbers starting from {@code from}, extending to {@code toInclusive}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.rangeClosed(0L, 0L)  // = ChampVectorSet(0L)
     * ChampVectorSet.rangeClosed(2L, 0L)  // = ChampVectorSet()
     * ChampVectorSet.rangeClosed(-2L, 2L) // = ChampVectorSet(-2L, -1L, 0L, 1L, 2L)
     * </code>
     * </pre>
     *
     * @param from        the first number
     * @param toInclusive the last number
     * @return a range of long values as specified or the empty range if {@code from > toInclusive}
     */
    public static ChampVectorSet<Long> rangeClosed(long from, long toInclusive) {
        return ChampVectorSet.ofAll(Iterator.rangeClosed(from, toInclusive));
    }

    /**
     * Creates a ChampVectorSet of int numbers starting from {@code from}, extending to {@code toInclusive},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.rangeClosedBy(1, 3, 1)  // = ChampVectorSet(1, 2, 3)
     * ChampVectorSet.rangeClosedBy(1, 4, 2)  // = ChampVectorSet(1, 3)
     * ChampVectorSet.rangeClosedBy(4, 1, -2) // = ChampVectorSet(4, 2)
     * ChampVectorSet.rangeClosedBy(4, 1, 2)  // = ChampVectorSet()
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
    public static ChampVectorSet<Integer> rangeClosedBy(int from, int toInclusive, int step) {
        return ChampVectorSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    public static ChampVectorSet<Character> rangeClosedBy(char from, char toInclusive, int step) {
        return ChampVectorSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    public static ChampVectorSet<Double> rangeClosedBy(double from, double toInclusive, double step) {
        return ChampVectorSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    /**
     * Creates a ChampVectorSet of long numbers starting from {@code from}, extending to {@code toInclusive},
     * with {@code step}.
     * <p>
     * Examples:
     * <pre>
     * <code>
     * ChampVectorSet.rangeClosedBy(1L, 3L, 1L)  // = ChampVectorSet(1L, 2L, 3L)
     * ChampVectorSet.rangeClosedBy(1L, 4L, 2L)  // = ChampVectorSet(1L, 3L)
     * ChampVectorSet.rangeClosedBy(4L, 1L, -2L) // = ChampVectorSet(4L, 2L)
     * ChampVectorSet.rangeClosedBy(4L, 1L, 2L)  // = ChampVectorSet()
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
    public static ChampVectorSet<Long> rangeClosedBy(long from, long toInclusive, long step) {
        return ChampVectorSet.ofAll(Iterator.rangeClosedBy(from, toInclusive, step));
    }

    /**
     * Returns a ChampVectorSet containing {@code n} values of a given Function {@code f}
     * over a range of integer values from 0 to {@code n - 1}.
     *
     * @param <T> Component type of the ChampVectorSet
     * @param n   The number of elements in the ChampVectorSet
     * @param f   The Function computing element values
     * @return A ChampVectorSet consisting of elements {@code f(0),f(1), ..., f(n - 1)}
     * @throws NullPointerException if {@code f} is null
     */
    public static <T> ChampVectorSet<T> tabulate(int n, Function<? super Integer, ? extends T> f) {
        Objects.requireNonNull(f, "f is null");
        return Collections.tabulate(n, f, ChampVectorSet.empty(), ChampVectorSet::of);
    }

    /**
     * Add the given element to this set, doing nothing if it is already contained.
     * <p>
     * Note that this method has a worst-case linear complexity.
     *
     * @param element The element to be added.
     * @return A new set containing all elements of this set and also {@code element}.
     */
    @Override
    public ChampVectorSet<T> add(T element) {
        return addLast(element, false);
    }

    /**
     * Adds all of the given elements to this set, replacing existing one if they are not already contained.
     * <p>
     * Note that this method has a worst-case quadratic complexity.
     *
     * @param elements The elements to be added.
     * @return A new set containing all elements of this set and the given {@code elements}, if not already contained.
     */
    @SuppressWarnings("unchecked")
    @Override
    public ChampVectorSet<T> addAll(Iterable<? extends T> elements) {
        if (isEmpty() && elements instanceof ChampVectorSet) {
            return (ChampVectorSet<T>) elements;
        }
        TransientLinkedHashSet<T> t = toTransient();
        t.addAll(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    private ChampVectorSet<T> addLast(T e, boolean moveToLast) {
        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<T>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<T>>();
        ChampSequenced.ChampSequencedElement<T> newElem = new ChampSequenced.ChampSequencedElement<T>(e, vector.size() - offset);
        ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<T>> newRoot = root.put(null, newElem,
                Objects.hashCode(e), 0, details,
                moveToLast ? ChampSequenced.ChampSequencedElement::updateAndMoveToLast : ChampSequenced.ChampSequencedElement::update,
                Objects::equals, Objects::hashCode);
        if (details.isModified()) {
            BitMappedTrie<Object> newVector = vector;
            int newOffset = offset;
            int newSize = size;
            if (details.isReplaced()) {
                if (moveToLast) {
                    ChampSequenced.ChampSequencedElement<T> oldElem = details.getOldData();
                    Tuple2<BitMappedTrie<Object>, Integer> result = vecRemove(newVector, oldElem, newOffset);
                    newVector = result._1;
                    newOffset = result._2;
                }
            } else {
                newSize++;
            }
            newVector = newVector.append(newElem);
            return renumber(newRoot, newVector, newSize, newOffset);
        }
        return this;
    }

    @Override
    public <R> ChampVectorSet<R> collect(PartialFunction<? super T, ? extends R> partialFunction) {
        return ofAll(iterator().<R>collect(partialFunction));
    }

    @Override
    public boolean contains(T element) {
        return root.find(new ChampSequenced.ChampSequencedElement<>(element), Objects.hashCode(element), 0, Objects::equals) != ChampTrie.Node.NO_DATA;
    }

    @Override
    public ChampVectorSet<T> diff(Set<? extends T> elements) {
        return removeAll(elements);
    }

    @Override
    public ChampVectorSet<T> distinct() {
        return this;
    }

    @Override
    public ChampVectorSet<T> distinctBy(Comparator<? super T> comparator) {
        Objects.requireNonNull(comparator, "comparator is null");
        return ChampVectorSet.ofAll(iterator().distinctBy(comparator));
    }

    @Override
    public <U> ChampVectorSet<T> distinctBy(Function<? super T, ? extends U> keyExtractor) {
        Objects.requireNonNull(keyExtractor, "keyExtractor is null");
        return ChampVectorSet.ofAll(iterator().distinctBy(keyExtractor));
    }

    @Override
    public ChampVectorSet<T> drop(int n) {
        if (n <= 0) {
            return this;
        } else {
            return ChampVectorSet.ofAll(iterator(n));
        }
    }

    @Override
    public ChampVectorSet<T> dropRight(int n) {
        if (n <= 0) {
            return this;
        } else {
            return ChampVectorSet.ofAll(iterator().dropRight(n));
        }
    }

    @Override
    public ChampVectorSet<T> dropUntil(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return dropWhile(predicate.negate());
    }

    @Override
    public ChampVectorSet<T> dropWhile(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        final ChampVectorSet<T> dropped = ChampVectorSet.ofAll(iterator().dropWhile(predicate));
        return dropped.length() == length() ? this : dropped;
    }

    @Override
    public boolean equals(Object o) {
        return Collections.equals(this, o);
    }

    @Override
    public ChampVectorSet<T> filter(Predicate<? super T> predicate) {
        TransientLinkedHashSet<T> t = toTransient();
        t.filterAll(predicate);
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public <U> ChampVectorSet<U> flatMap(Function<? super T, ? extends Iterable<? extends U>> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        ChampVectorSet<U> flatMapped = empty();
        for (T t : this) {
            for (U u : mapper.apply(t)) {
                flatMapped = flatMapped.add(u);
            }
        }
        return flatMapped;
    }

    @Override
    public <U> U foldRight(U zero, BiFunction<? super T, ? super U, ? extends U> f) {
        Objects.requireNonNull(f, "f is null");
        return iterator().foldRight(zero, f);
    }

    @Override
    public <C> Map<C, ChampVectorSet<T>> groupBy(Function<? super T, ? extends C> classifier) {
        return Collections.groupBy(this, classifier, ChampVectorSet::ofAll, ChampVectorMap.empty());
    }

    @Override
    public Iterator<ChampVectorSet<T>> grouped(int size) {
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

    @SuppressWarnings("unchecked")
    @Override
    public T head() {
        return ((ChampSequenced.ChampSequencedElement<T>) vector.head()).getElement();
    }

    @Override
    public Option<T> headOption() {
        return isEmpty() ? Option.none() : Option.some(head());
    }

    @Override
    public ChampVectorSet<T> init() {
        // XXX Traversable.init() specifies that we must throw
        //     UnsupportedOperationException instead of NoSuchElementException
        //     when this set is empty.
        if (isEmpty()) {
            throw new UnsupportedOperationException();
        }
        return remove(last());
    }

    @Override
    public Option<ChampVectorSet<T>> initOption() {
        return isEmpty() ? Option.none() : Option.some(init());
    }

    @Override
    public ChampVectorSet<T> intersect(Set<? extends T> elements) {
        return retainAll(elements);
    }

    /**
     * An {@code ChampVectorSet}'s value is computed synchronously.
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
     * An {@code ChampVectorSet}'s value is computed eagerly.
     *
     * @return false
     */
    @Override
    public boolean isLazy() {
        return false;
    }

    @Override
    public boolean isSequential() {
        return true;
    }

    @Override
    public boolean isTraversableAgain() {
        return true;
    }

    @Override
    public Iterator<T> iterator() {
        return new ChampIteration.IteratorFacade<>(spliterator());
    }

    Iterator<T> iterator(int startIndex) {
        return new ChampIteration.IteratorFacade<>(spliterator(startIndex));
    }

    @SuppressWarnings("unchecked")
    @Override
    public T last() {
        return ((ChampSequenced.ChampSequencedElement<T>) vector.last()).getElement();
    }

    @Override
    public int length() {
        return size;
    }

    @Override
    public <U> ChampVectorSet<U> map(Function<? super T, ? extends U> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        ChampVectorSet<U> mapped = empty();
        for (T t : this) {
            mapped = mapped.add(mapper.apply(t));
        }
        return mapped;
    }

    @Override
    public String mkString(CharSequence prefix, CharSequence delimiter, CharSequence suffix) {
        return iterator().mkString(prefix, delimiter, suffix);
    }

    @Override
    public ChampVectorSet<T> orElse(Iterable<? extends T> other) {
        return isEmpty() ? ofAll(other) : this;
    }

    @Override
    public ChampVectorSet<T> orElse(Supplier<? extends Iterable<? extends T>> supplier) {
        return isEmpty() ? ofAll(supplier.get()) : this;
    }

    @Override
    public Tuple2<ChampVectorSet<T>, ChampVectorSet<T>> partition(Predicate<? super T> predicate) {
        return Collections.partition(this, ChampVectorSet::ofAll, predicate);
    }

    @Override
    public ChampVectorSet<T> peek(Consumer<? super T> action) {
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
    public ChampVectorSet<T> reject(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.filter(predicate.negate());
    }

    @Override
    public ChampVectorSet<T> remove(T element) {
        int keyHash = Objects.hashCode(element);
        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<T>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<T>>();
        ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<T>> newRoot = root.remove(null,
                new ChampSequenced.ChampSequencedElement<>(element),
                keyHash, 0, details, Objects::equals);
        if (details.isModified()) {
            ChampSequenced.ChampSequencedElement<T> removedElem = details.getOldDataNonNull();
            Tuple2<BitMappedTrie<Object>, Integer> result = vecRemove(vector, removedElem, offset);
            return renumber(newRoot, result._1, size - 1,
                    result._2);
        }
        return this;
    }

    @Override
    public ChampVectorSet<T> removeAll(Iterable<? extends T> elements) {
        TransientLinkedHashSet<T> t = toTransient();
        t.removeAll(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    /**
     * Renumbers the sequenced elements in the trie if necessary.
     *
     * @param root   the root of the trie
     * @param vector the root of the vector
     * @param size   the size of the trie
     * @param offset the offset that must be added to a sequence number to get the index into the vector
     * @return a new {@link ChampVectorSet} instance
     */
    private ChampVectorSet<T> renumber(
            ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<T>> root,
            BitMappedTrie<Object> vector,
            int size, int offset) {

        if (ChampSequenced.ChampSequencedData.vecMustRenumber(size, offset, this.vector.size())) {
            ChampTrie.IdentityObject owner = new ChampTrie.IdentityObject();
            Tuple2<ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<T>>, BitMappedTrie<Object>> result = ChampSequenced.ChampSequencedData.<ChampSequenced.ChampSequencedElement<T>>vecRenumber(
                    size, root, vector, owner, Objects::hashCode, Objects::equals,
                    (e, seq) -> new ChampSequenced.ChampSequencedElement<>(e.getElement(), seq));
            return new ChampVectorSet<>(
                    result._1(), result._2(),
                    size, 0);
        }
        return new ChampVectorSet<>(root, vector, size, offset);
    }

    @Override
    public ChampVectorSet<T> replace(T currentElement, T newElement) {
        // currentElement and newElem are the same => do nothing
        if (Objects.equals(currentElement, newElement)) {
            return this;
        }

        // try to remove currentElem from the 'root' trie
        final ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<T>> detailsCurrent = new ChampTrie.ChangeEvent<>();
        ChampTrie.IdentityObject owner = new ChampTrie.IdentityObject();
        ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<T>> newRoot = root.remove(owner,
                new ChampSequenced.ChampSequencedElement<>(currentElement),
                Objects.hashCode(currentElement), 0, detailsCurrent, Objects::equals);
        // currentElement was not in the 'root' trie => do nothing
        if (!detailsCurrent.isModified()) {
            return this;
        }

        // currentElement was in the 'root' trie, and we have just removed it
        // => also remove its entry from the 'sequenceRoot' trie
        BitMappedTrie<Object> newVector = vector;
        int newOffset = offset;
        ChampSequenced.ChampSequencedElement<T> currentData = detailsCurrent.getOldData();
        int seq = currentData.getSequenceNumber();
        Tuple2<BitMappedTrie<Object>, Integer> result = vecRemove(newVector, currentData, newOffset);
        newVector = result._1;
        newOffset = result._2;

        // try to update the trie with the newElement
        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<T>> detailsNew = new ChampTrie.ChangeEvent<>();
        ChampSequenced.ChampSequencedElement<T> newData = new ChampSequenced.ChampSequencedElement<>(newElement, seq);
        newRoot = newRoot.put(owner,
                newData, Objects.hashCode(newElement), 0, detailsNew,
                ChampSequenced.ChampSequencedElement::forceUpdate,
                Objects::equals, Objects::hashCode);
        boolean isReplaced = detailsNew.isReplaced();

        // there already was an element with key newElement._1 in the trie, and we have just replaced it
        // => remove the replaced entry from the 'sequenceRoot' trie
        if (isReplaced) {
            ChampSequenced.ChampSequencedElement<T> replacedEntry = detailsNew.getOldData();
            result = vecRemove(newVector, replacedEntry, newOffset);
            newVector = result._1;
            newOffset = result._2;
        }

        // we have just successfully added or replaced the newElement
        // => insert the new entry in the 'sequenceRoot' trie
        newVector = seq + newOffset < newVector.size() ? newVector.update(seq + newOffset, newData) : newVector.append(newData);

        if (isReplaced) {
            // we reduced the size of the map by one => renumbering may be necessary
            return renumber(newRoot, newVector, size - 1, newOffset);
        } else {
            // we did not change the size of the map => no renumbering is needed
            return new ChampVectorSet<>(newRoot, newVector, size, newOffset);
        }
    }

    @Override
    public ChampVectorSet<T> replaceAll(T currentElement, T newElement) {
        return replace(currentElement, newElement);
    }

    @Override
    public ChampVectorSet<T> retainAll(Iterable<? extends T> elements) {
        TransientLinkedHashSet<T> t = toTransient();
        t.retainAll(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    private Iterator<T> reverseIterator() {
        return new ChampIteration.IteratorFacade<>(reverseSpliterator());
    }

    @SuppressWarnings("unchecked")
    private Spliterator<T> reverseSpliterator() {
        return new ChampSequenced.ChampReverseVectorSpliterator<>(vector,
                e -> ((ChampSequenced.ChampSequencedElement<T>) e).getElement(),
                0, size(), Spliterator.SIZED | Spliterator.DISTINCT | Spliterator.ORDERED | Spliterator.IMMUTABLE);
    }

    @Override
    public ChampVectorSet<T> scan(T zero, BiFunction<? super T, ? super T, ? extends T> operation) {
        return scanLeft(zero, operation);
    }

    @Override
    public <U> ChampVectorSet<U> scanLeft(U zero, BiFunction<? super U, ? super T, ? extends U> operation) {
        return Collections.scanLeft(this, zero, operation, ChampVectorSet::ofAll);
    }

    @Override
    public <U> ChampVectorSet<U> scanRight(U zero, BiFunction<? super T, ? super U, ? extends U> operation) {
        return Collections.scanRight(this, zero, operation, ChampVectorSet::ofAll);
    }

    @Override
    public Iterator<ChampVectorSet<T>> slideBy(Function<? super T, ?> classifier) {
        return iterator().slideBy(classifier).map(ChampVectorSet::ofAll);
    }

    @Override
    public Iterator<ChampVectorSet<T>> sliding(int size) {
        return sliding(size, 1);
    }

    @Override
    public Iterator<ChampVectorSet<T>> sliding(int size, int step) {
        return iterator().sliding(size, step).map(ChampVectorSet::ofAll);
    }

    @Override
    public Tuple2<ChampVectorSet<T>, ChampVectorSet<T>> span(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        final Tuple2<Iterator<T>, Iterator<T>> t = iterator().span(predicate);
        return Tuple.of(ChampVectorSet.ofAll(t._1), ChampVectorSet.ofAll(t._2));
    }

    @SuppressWarnings("unchecked")
    @Override
    public Spliterator<T> spliterator() {
        return spliterator(0);
    }

    @SuppressWarnings("unchecked")
    Spliterator<T> spliterator(int startIndex) {
        return new ChampSequenced.ChampVectorSpliterator<>(vector,
                e -> ((ChampSequenced.ChampSequencedElement<T>) e).getElement(),
                startIndex, size(), Spliterator.SIZED | Spliterator.DISTINCT | Spliterator.ORDERED | Spliterator.IMMUTABLE);
    }

    @Override
    public String stringPrefix() {
        return "ChampVectorSet";
    }

    @Override
    public ChampVectorSet<T> tail() {
        // XXX AbstractTraversableTest.shouldThrowWhenTailOnNil requires that we throw UnsupportedOperationException instead of NoSuchElementException.
        if (isEmpty()) throw new UnsupportedOperationException();
        return remove(head());
    }

    @Override
    public Option<ChampVectorSet<T>> tailOption() {
        return isEmpty() ? Option.none() : Option.some(tail());
    }

    @Override
    public ChampVectorSet<T> take(int n) {
        if (size() <= n) {
            return this;
        }
        return ChampVectorSet.ofAll(() -> iterator().take(n));
    }

    @Override
    public ChampVectorSet<T> takeRight(int n) {
        if (size() <= n) {
            return this;
        }
        return ChampVectorSet.ofAll(() -> iterator().takeRight(n));
    }

    @Override
    public ChampVectorSet<T> takeUntil(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return takeWhile(predicate.negate());
    }

    @Override
    public ChampVectorSet<T> takeWhile(Predicate<? super T> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        final ChampVectorSet<T> taken = ChampVectorSet.ofAll(iterator().takeWhile(predicate));
        return taken.length() == length() ? this : taken;
    }

    @Override
    public java.util.LinkedHashSet<T> toJavaSet() {
        // XXX If the return value was not required to be a java.util.ChampVectorSet
        //     we could provide a mutable ChampVectorSet in O(1)
        return toJavaSet(java.util.LinkedHashSet::new);
    }

    @Override
    public <K, V> Map<K, V> toLinkedMap(Function<? super T, ? extends Tuple2<? extends K, ? extends V>> f) {
        Objects.requireNonNull(f, "f is null");
        Function<Tuple2<? extends K, ? extends V>, io.vavr.collection.Map<K, V>> ofElement = ChampVectorMap::of;
        Function<Iterable<Tuple2<? extends K, ? extends V>>, io.vavr.collection.Map<K, V>> ofAll = ChampVectorMap::ofEntries;
        return ValueModule.toMap(this, ChampVectorMap.empty(), ofElement, ofAll, f);
    }

    @Override
    public <K, V> Map<K, V> toLinkedMap(Function<? super T, ? extends K> keyMapper, Function<? super T, ? extends V> valueMapper) {
        return Set.super.toLinkedMap(keyMapper, valueMapper);
    }

    @Override
    public Set<T> toLinkedSet() {
        return (io.vavr.collection.Set) ValueModule.toTraversable(this, ChampVectorSet.empty(), ChampVectorSet::of, ChampVectorSet::ofAll);
    }

    @Override
    public <K, V> Map<K, V> toMap(Function<? super T, ? extends Tuple2<? extends K, ? extends V>> f) {
        Objects.requireNonNull(f, "f is null");
        Function<Tuple2<? extends K, ? extends V>, io.vavr.collection.Map<K, V>> ofElement = ChampMap::of;
        Function<Iterable<Tuple2<? extends K, ? extends V>>, io.vavr.collection.Map<K, V>> ofAll = ChampMap::ofEntries;
        return ValueModule.toMap(this, ChampMap.empty(), ofElement, ofAll, f);

    }

    @Override
    public <K, V> Map<K, V> toMap(Function<? super T, ? extends K> keyMapper, Function<? super T, ? extends V> valueMapper) {
        return Set.super.toMap(keyMapper, valueMapper);
    }

    @Override
    public Set<T> toSet() {
        return this;
    }

    @Override
    public String toString() {
        return mkString(stringPrefix() + "(", ", ", ")");
    }

    // -- Object

    TransientLinkedHashSet<T> toTransient() {
        return new TransientLinkedHashSet<>(this);
    }

    /**
     * Transforms this {@code ChampVectorSet}.
     *
     * @param f   A transformation
     * @param <U> Type of transformation result
     * @return An instance of type {@code U}
     * @throws NullPointerException if {@code f} is null
     */
    public <U> U transform(Function<? super ChampVectorSet<T>, ? extends U> f) {
        Objects.requireNonNull(f, "f is null");
        return f.apply(this);
    }

    /**
     * Adds all of the elements of {@code that} set to this set, if not already present.
     *
     * @param elements The set to form the union with.
     * @return A new set that contains all distinct elements of this and {@code elements} set.
     */
    @Override
    public ChampVectorSet<T> union(Set<? extends T> elements) {
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

    // -- Serialization

    public <T1, T2> Tuple2<ChampVectorSet<T1>, ChampVectorSet<T2>> unzip(Function<? super T, Tuple2<? extends T1, ? extends T2>> unzipper) {
        Objects.requireNonNull(unzipper, "unzipper is null");
        Tuple2<Iterator<T1>, Iterator<T2>> t = this.iterator().unzip(unzipper);
        return Tuple.of(ofAll((Iterable) t._1), ofAll((Iterable) t._2));
    }

    public <T1, T2, T3> Tuple3<ChampVectorSet<T1>, ChampVectorSet<T2>, ChampVectorSet<T3>> unzip3(Function<? super T, Tuple3<? extends T1, ? extends T2, ? extends T3>> unzipper) {
        Objects.requireNonNull(unzipper, "unzipper is null");
        Tuple3<Iterator<T1>, Iterator<T2>, Iterator<T3>> t = this.iterator().unzip3(unzipper);
        return Tuple.of(ofAll((Iterable) t._1), ofAll((Iterable) t._2), ofAll((Iterable) t._3));
    }

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
    public <U> ChampVectorSet<Tuple2<T, U>> zip(Iterable<? extends U> that) {
        return zipWith(that, Tuple::of);
    }

    @Override
    public <U> ChampVectorSet<Tuple2<T, U>> zipAll(Iterable<? extends U> that, T thisElem, U thatElem) {
        Objects.requireNonNull(that, "that is null");
        return ChampVectorSet.ofAll(iterator().zipAll(that, thisElem, thatElem));
    }

    @Override
    public <U, R> ChampVectorSet<R> zipWith(Iterable<? extends U> that, BiFunction<? super T, ? super U, ? extends R> mapper) {
        Objects.requireNonNull(that, "that is null");
        Objects.requireNonNull(mapper, "mapper is null");
        return ChampVectorSet.ofAll(iterator().zipWith(that, mapper));
    }

    @Override
    public ChampVectorSet<Tuple2<T, Integer>> zipWithIndex() {
        return zipWithIndex(Tuple::of);
    }

    @Override
    public <U> ChampVectorSet<U> zipWithIndex(BiFunction<? super T, ? super Integer, ? extends U> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        return ChampVectorSet.ofAll(iterator().zipWithIndex(mapper));
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
        private transient ChampVectorSet<T> set;

        /**
         * Constructor for the case of serialization, called by {@link ChampVectorSet#writeReplace()}.
         * <p/>
         * The constructor of a SerializationProxy takes an argument that concisely represents the logical state of
         * an instance of the enclosing class.
         *
         * @param set a Cons
         */
        SerializationProxy(ChampVectorSet<T> set) {
            this.set = set;
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
            ChampVectorSet<T> temp = ChampVectorSet.empty();
            for (int i = 0; i < size; i++) {
                @SuppressWarnings("unchecked") final T element = (T) s.readObject();
                temp = temp.add(element);
            }
            set = temp;
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
            return ChampVectorSet.empty().addAll(set);
        }

        /**
         * Write an object to a serialization stream.
         *
         * @param s An object serialization stream.
         * @throws IOException If an error occurs writing to the stream.
         */
        private void writeObject(ObjectOutputStream s) throws IOException {
            s.defaultWriteObject();
            s.writeInt(set.size());
            for (T e : set) {
                s.writeObject(e);
            }
        }
    }

    /**
     * Supports efficient bulk-operations on a linked hash set through transience.
     *
     * @param <E>the element type
     */
    static class TransientLinkedHashSet<E> extends ChampTransience.ChampAbstractTransientSet<E, ChampSequenced.ChampSequencedElement<E>> {
        int offset;
        BitMappedTrie<Object> vector;

        TransientLinkedHashSet(ChampVectorSet<E> s) {
            root = s.root;
            size = s.size;
            this.vector = s.vector;
            this.offset = s.offset;
        }

        TransientLinkedHashSet() {
            this(empty());
        }

        boolean add(E element) {
            return addLast(element, false);
        }

        @SuppressWarnings("unchecked")
        boolean addAll(Iterable<? extends E> c) {
            if (c == root) {
                return false;
            }
            if (isEmpty() && (c instanceof ChampVectorSet<?>)) {
                ChampVectorSet<?> cc = (ChampVectorSet<?>) c;
                root = (ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<E>>) (ChampTrie.BitmapIndexedNode<?>) cc.root;
                size = cc.size;
                return true;
            }
            boolean modified = false;
            for (E e : c) {
                modified |= add(e);
            }
            return modified;
        }

        private boolean addLast(E e, boolean moveToLast) {
            ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<E>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<E>>();
            ChampSequenced.ChampSequencedElement<E> newElem = new ChampSequenced.ChampSequencedElement<E>(e, vector.size() - offset);
            root = root.put(makeOwner(), newElem,
                    Objects.hashCode(e), 0, details,
                    moveToLast ? ChampSequenced.ChampSequencedElement::updateAndMoveToLast : ChampSequenced.ChampSequencedElement::update,
                    Objects::equals, Objects::hashCode);
            if (details.isModified()) {

                if (details.isReplaced()) {
                    if (moveToLast) {
                        ChampSequenced.ChampSequencedElement<E> oldElem = details.getOldData();
                        Tuple2<BitMappedTrie<Object>, Integer> result = vecRemove(vector, oldElem, offset);
                        vector = result._1;
                        offset = result._2;
                    }
                } else {
                    size++;
                }
                vector = vector.append(newElem);
                renumber();
                return true;
            }
            return false;
        }

        @Override
        void clear() {
            root = emptyNode();
            vector = BitMappedTrie.empty();
            size = 0;
            modCount++;
            offset = -1;
        }

        boolean filterAll(Predicate<? super E> predicate) {
            VectorSideEffectPredicate<E> vp = new VectorSideEffectPredicate<>(predicate, vector, offset);
            ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
            ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<E>> newRootNode = root.filterAll(makeOwner(), vp, 0, bulkChange);
            if (bulkChange.removed == 0) {
                return false;
            }
            root = newRootNode;
            vector = vp.newVector;
            offset = vp.newOffset;
            size -= bulkChange.removed;
            modCount++;
            return true;
        }

        @Override
        java.util.Iterator<E> iterator() {
            return new ChampIteration.IteratorFacade<>(spliterator());
        }

        @SuppressWarnings("unchecked")
        @Override
        boolean remove(Object element) {
            int keyHash = Objects.hashCode(element);
            ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<E>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedElement<E>>();
            root = root.remove(makeOwner(),
                    new ChampSequenced.ChampSequencedElement<>((E) element),
                    keyHash, 0, details, Objects::equals);
            if (details.isModified()) {
                ChampSequenced.ChampSequencedElement<E> removedElem = details.getOldDataNonNull();
                Tuple2<BitMappedTrie<Object>, Integer> result = vecRemove(vector, removedElem, offset);
                vector = result._1;
                offset = result._2;
                size--;
                renumber();
                return true;
            }
            return false;
        }

        private void renumber() {
            if (ChampSequenced.ChampSequencedData.vecMustRenumber(size, offset, vector.size())) {
                ChampTrie.IdentityObject owner = new ChampTrie.IdentityObject();
                Tuple2<ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedElement<E>>, BitMappedTrie<Object>> result = ChampSequenced.ChampSequencedData.<ChampSequenced.ChampSequencedElement<E>>vecRenumber(
                        size, root, vector, owner, Objects::hashCode, Objects::equals,
                        (e, seq) -> new ChampSequenced.ChampSequencedElement<>(e.getElement(), seq));
                root = result._1;
                vector = result._2;
                offset = 0;
            }
        }

        @SuppressWarnings("unchecked")
        Spliterator<E> spliterator() {
            return new ChampSequenced.ChampVectorSpliterator<>(vector,
                    (Object o) -> ((ChampSequenced.ChampSequencedElement<E>) o).getElement(), 0,
                    size(), Spliterator.SIZED | Spliterator.DISTINCT | Spliterator.ORDERED);
        }

        public ChampVectorSet<E> toImmutable() {
            owner = null;
            return isEmpty()
                    ? empty()
                    : new ChampVectorSet<>(root, vector, size, offset);
        }

        static class VectorSideEffectPredicate<E> implements Predicate<ChampSequenced.ChampSequencedElement<E>> {
            BitMappedTrie<Object> newVector;
            int newOffset;
            Predicate<? super E> predicate;

            public VectorSideEffectPredicate(Predicate<? super E> predicate, BitMappedTrie<Object> vector, int offset) {
                this.predicate = predicate;
                this.newVector = vector;
                this.newOffset = offset;
            }

            @Override
            public boolean test(ChampSequenced.ChampSequencedElement<E> e) {
                if (!predicate.test(e.getElement())) {
                    Tuple2<BitMappedTrie<Object>, Integer> result = vecRemove(newVector, e, newOffset);
                    newVector = result._1;
                    newOffset = result._2;
                    return false;
                }
                return true;
            }
        }
    }
}
