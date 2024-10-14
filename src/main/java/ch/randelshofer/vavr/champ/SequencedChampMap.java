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

import io.vavr.Tuple;
import io.vavr.Tuple2;
import io.vavr.collection.Seq;
import io.vavr.collection.Set;
import io.vavr.control.Option;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Map;
import java.util.Objects;
import java.util.Spliterator;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collector;

import static ch.randelshofer.vavr.champ.ChampSequenced.ChampSequencedData.vecRemove;
import static ch.randelshofer.vavr.champ.ChampTrie.BitmapIndexedNode.emptyNode;

/**
 * Implements an immutable map using a Compressed Hash-Array Mapped Prefix-tree
 * (CHAMP) and a bit-mapped trie (BitMappedTrie).
 * <p>
 * Features:
 * <ul>
 *     <li>supports up to 2<sup>30</sup> entries</li>
 *     <li>allows null keys and null values</li>
 *     <li>is immutable</li>
 *     <li>is thread-safe</li>
 *     <li>iterates in the order, in which keys were inserted</li>
 * </ul>
 * <p>
 * Performance characteristics:
 * <ul>
 *     <li>put, putFirst, putLast: O(log N) in an amortized sense, because we sometimes have to
 *     renumber the elements.</li>
 *     <li>remove: O(log N) in an amortized sense, because we sometimes have to renumber the elements.</li>
 *     <li>containsKey: O(1)</li>
 *     <li>toMutable: O(1) + O(log N) distributed across subsequent updates in
 *     the mutable copy</li>
 *     <li>clone: O(1)</li>
 *     <li>iterator creation: O(1)</li>
 *     <li>iterator.next: O(log N)</li>
 *     <li>getFirst, getLast: O(log N)</li>
 * </ul>
 * <p>
 * Implementation details:
 * <p>
 * This map performs read and write operations of single elements in O(log N) time,
 * and in O(log N) space, where N is the number of elements in the set.
 * <p>
 * The CHAMP trie contains nodes that may be shared with other maps.
 * <p>
 * If a write operation is performed on a node, then this set creates a
 * copy of the node and of all parent nodes up to the root (copy-path-on-write).
 * Since the CHAMP trie has a fixed maximal height, the cost is O(1).
 * <p>
 * Insertion Order:
 * <p>
 * This map uses a counter to keep track of the insertion order.
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
 * Portions of the code in this class have been derived from JHotDraw8 'VectorMap.java'.
 * <p>
 * For a similar design, see 'VectorMap.scala'. Note, that this code is not a derivative
 * of that code.
 * <dl>
 *     <dt>JHotDraw 8. VectorMap.java. Copyright © 2023 The authors and contributors of JHotDraw.
 *     <a href="https://github.com/wrandelshofer/jhotdraw8/blob/8c1a98b70bc23a0c63f1886334d5b568ada36944/LICENSE">MIT License</a>.</dt>
 *     <dd><a href="https://github.com/wrandelshofer/jhotdraw8">github.com</a></dd>
 *     <dt>The Scala library. VectorMap.scala. Copyright EPFL and Lightbend, Inc. Apache License 2.0.</dt>
 *     <dd><a href="https://github.com/scala/scala/blob/28eef15f3cc46f6d3dd1884e94329d7601dc20ee/src/library/scala/collection/immutable/VectorMap.scala">github.com</a>
 *     </dd>
 * </dl>
 *
 * @param <K> the key type
 * @param <V> the value type
 */
@SuppressWarnings("exports")
public class SequencedChampMap<K, V> implements io.vavr.collection.Map<K, V>, Serializable {
    private static final long serialVersionUID = 1L;
    private static final SequencedChampMap<?, ?> EMPTY = new SequencedChampMap<>(
            emptyNode(), BitMappedTrie.empty(), 0, 0);
    /**
     * Offset of sequence numbers to vector indices.
     *
     * <pre>vector index = sequence number + offset</pre>
     */
    final int offset;
    /**
     * The size of the map.
     */
    final int size;
    /**
     * In this vector we store the elements in the order in which they were inserted.
     */
    final BitMappedTrie<Object> vector;
    private final ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>> root;

    SequencedChampMap(ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>> root,
                      BitMappedTrie<Object> vector,
                      int size, int offset) {
        this.root = root;
        this.size = size;
        this.offset = offset;
        this.vector = Objects.requireNonNull(vector);
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link SequencedChampMap}.
     *
     * @param <K> The key type
     * @param <V> The value type
     * @return A {@link SequencedChampMap} Collector.
     */
    public static <K, V> Collector<Tuple2<K, V>, ArrayList<Tuple2<K, V>>, SequencedChampMap<K, V>> collector() {
        return Collections.toListAndThen(SequencedChampMap::ofEntries);
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link SequencedChampMap}.
     *
     * @param keyMapper The key mapper
     * @param <K>       The key type
     * @param <V>       The value type
     * @param <T>       Initial {@link java.util.stream.Stream} elements type
     * @return A {@link SequencedChampMap} Collector.
     */
    public static <K, V, T extends V> Collector<T, ArrayList<T>, SequencedChampMap<K, V>> collector(Function<? super T, ? extends K> keyMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        return SequencedChampMap.collector(keyMapper, v -> v);
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link SequencedChampMap}.
     *
     * @param keyMapper   The key mapper
     * @param valueMapper The value mapper
     * @param <K>         The key type
     * @param <V>         The value type
     * @param <T>         Initial {@link java.util.stream.Stream} elements type
     * @return A {@link SequencedChampMap} Collector.
     */
    public static <K, V, T> Collector<T, ArrayList<T>, SequencedChampMap<K, V>> collector(
            Function<? super T, ? extends K> keyMapper, Function<? super T, ? extends V> valueMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        Objects.requireNonNull(valueMapper, "valueMapper is null");
        return Collections.toListAndThen(arr -> SequencedChampMap.ofEntries(io.vavr.collection.Iterator.ofAll(arr)
                .map(t -> Tuple.of(keyMapper.apply(t), valueMapper.apply(t)))));
    }

    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> empty() {
        return (SequencedChampMap<K, V>) EMPTY;
    }

    /**
     * Returns a SequencedChampMap containing tuples returned by {@code n} calls to a given Supplier {@code s}.
     *
     * @param <K> The key type
     * @param <V> The value type
     * @param n   The number of elements in the SequencedChampMap
     * @param s   The Supplier computing element values
     * @return A SequencedChampMap of size {@code n}, where each element contains the result supplied by {@code s}.
     * @throws NullPointerException if {@code s} is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> fill(int n, Supplier<? extends Tuple2<? extends K, ? extends V>> s) {
        Objects.requireNonNull(s, "s is null");
        return ofEntries(Collections.fill(n, (Supplier<? extends Tuple2<K, V>>) s));
    }

    /**
     * Narrows a widened {@code SequencedChampMap<? extends K, ? extends V>} to {@code SequencedChampMap<K, V>}
     * by performing a type-safe cast. This is eligible because immutable/read-only
     * collections are covariant.
     *
     * @param linkedHashMap A {@code SequencedChampMap}.
     * @param <K>           Key type
     * @param <V>           Value type
     * @return the given {@code linkedHashMap} instance as narrowed type {@code SequencedChampMap<K, V>}.
     */
    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> narrow(SequencedChampMap<? extends K, ? extends V> linkedHashMap) {
        return (SequencedChampMap<K, V>) linkedHashMap;
    }

    /**
     * Returns a singleton {@code SequencedChampMap}, i.e. a {@code SequencedChampMap} of one element.
     *
     * @param entry A map entry.
     * @param <K>   The key type
     * @param <V>   The value type
     * @return A new Map containing the given entry
     */
    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> of(Tuple2<? extends K, ? extends V> entry) {
        Objects.requireNonNull(entry, "entry is null");
        return SequencedChampMap.<K, V>empty().put(entry._1, entry._2);
    }

    /**
     * Returns a singleton {@code SequencedChampMap}, i.e. a {@code SequencedChampMap} of one element.
     *
     * @param key   A singleton map key.
     * @param value A singleton map value.
     * @param <K>   The key type
     * @param <V>   The value type
     * @return A new Map containing the given entry
     */
    public static <K, V> SequencedChampMap<K, V> of(K key, V value) {
        return SequencedChampMap.<K, V>empty().put(key, value);
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        t.put(k4, v4);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @param k5  a key for the map
     * @param v5  the value for k5
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        t.put(k4, v4);
        t.put(k5, v5);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @param k5  a key for the map
     * @param v5  the value for k5
     * @param k6  a key for the map
     * @param v6  the value for k6
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        t.put(k4, v4);
        t.put(k5, v5);
        t.put(k6, v6);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @param k5  a key for the map
     * @param v5  the value for k5
     * @param k6  a key for the map
     * @param v6  the value for k6
     * @param k7  a key for the map
     * @param v7  the value for k7
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        t.put(k4, v4);
        t.put(k5, v5);
        t.put(k6, v6);
        t.put(k7, v7);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @param k5  a key for the map
     * @param v5  the value for k5
     * @param k6  a key for the map
     * @param v6  the value for k6
     * @param k7  a key for the map
     * @param v7  the value for k7
     * @param k8  a key for the map
     * @param v8  the value for k8
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        t.put(k4, v4);
        t.put(k5, v5);
        t.put(k6, v6);
        t.put(k7, v7);
        t.put(k8, v8);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @param k5  a key for the map
     * @param v5  the value for k5
     * @param k6  a key for the map
     * @param v6  the value for k6
     * @param k7  a key for the map
     * @param v7  the value for k7
     * @param k8  a key for the map
     * @param v8  the value for k8
     * @param k9  a key for the map
     * @param v9  the value for k9
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8, K k9, V v9) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        t.put(k4, v4);
        t.put(k5, v5);
        t.put(k6, v6);
        t.put(k7, v7);
        t.put(k8, v8);
        t.put(k9, v9);
        return t.toImmutable();
    }

    /**
     * Creates a SequencedChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @param k5  a key for the map
     * @param v5  the value for k5
     * @param k6  a key for the map
     * @param v6  the value for k6
     * @param k7  a key for the map
     * @param v7  the value for k7
     * @param k8  a key for the map
     * @param v8  the value for k8
     * @param k9  a key for the map
     * @param v9  the value for k9
     * @param k10 a key for the map
     * @param v10 the value for k10
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> SequencedChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8, K k9, V v9, K k10, V v10) {
        TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<K, V>();
        t.put(k1, v1);
        t.put(k2, v2);
        t.put(k3, v3);
        t.put(k4, v4);
        t.put(k5, v5);
        t.put(k6, v6);
        t.put(k7, v7);
        t.put(k8, v8);
        t.put(k9, v9);
        t.put(k10, v10);
        return t.toImmutable();
    }

    /**
     * Returns a {@code SequencedChampMap}, from a source java.util.Map.
     *
     * @param map A map
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given map
     */
    public static <K, V> SequencedChampMap<K, V> ofAll(Map<? extends K, ? extends V> map) {
        Objects.requireNonNull(map, "map is null");
        TransientLinkedHashMap<K, V> m = new TransientLinkedHashMap<>();
        m.putAllEntries(map.entrySet());
        return m.toImmutable();
    }

    /**
     * Returns a {@code SequencedChampMap}, from entries mapped from stream.
     *
     * @param stream      the source stream
     * @param entryMapper the entry mapper
     * @param <T>         The stream element type
     * @param <K>         The key type
     * @param <V>         The value type
     * @return A new Map
     */
    public static <T, K, V> SequencedChampMap<K, V> ofAll(java.util.stream.Stream<? extends T> stream,
                                                          Function<? super T, Tuple2<? extends K, ? extends V>> entryMapper) {
        return Maps.ofStream(empty(), stream, entryMapper);
    }

    /**
     * Returns a {@code SequencedChampMap}, from entries mapped from stream.
     *
     * @param stream      the source stream
     * @param keyMapper   the key mapper
     * @param valueMapper the value mapper
     * @param <T>         The stream element type
     * @param <K>         The key type
     * @param <V>         The value type
     * @return A new Map
     */
    public static <T, K, V> SequencedChampMap<K, V> ofAll(java.util.stream.Stream<? extends T> stream,
                                                          Function<? super T, ? extends K> keyMapper,
                                                          Function<? super T, ? extends V> valueMapper) {
        return Maps.ofStream(empty(), stream, keyMapper, valueMapper);
    }

    /**
     * Creates a SequencedChampMap of the given entries.
     *
     * @param entries Map entries
     * @param <K>     The key type
     * @param <V>     The value type
     * @return A new Map containing the given entries
     */
    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> ofEntries(Map.Entry<? extends K, ? extends V>... entries) {
        return SequencedChampMap.<K, V>empty().putAllEntries(Arrays.asList(entries));
    }

    /**
     * Creates a SequencedChampMap of the given entries.
     *
     * @param entries Map entries
     * @param <K>     The key type
     * @param <V>     The value type
     * @return A new Map containing the given entries
     */
    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> ofEntries(Tuple2<? extends K, ? extends V>... entries) {
        return SequencedChampMap.<K, V>empty().putAllTuples(Arrays.asList(entries));
    }

    /**
     * Creates a SequencedChampMap of the given entries.
     *
     * @param entries Map entries
     * @param <K>     The key type
     * @param <V>     The value type
     * @return A new Map containing the given entries
     */
    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> ofEntries(Iterable<? extends Tuple2<? extends K, ? extends V>> entries) {
        Objects.requireNonNull(entries, "entries is null");
        return SequencedChampMap.<K, V>empty().putAllTuples(entries);
    }

    /**
     * Returns a SequencedChampMap containing {@code n} values of a given Function {@code f}
     * over a range of integer values from 0 to {@code n - 1}.
     *
     * @param <K> The key type
     * @param <V> The value type
     * @param n   The number of elements in the SequencedChampMap
     * @param f   The Function computing element values
     * @return A SequencedChampMap consisting of elements {@code f(0),f(1), ..., f(n - 1)}
     * @throws NullPointerException if {@code f} is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> SequencedChampMap<K, V> tabulate(int n, Function<? super Integer, ? extends Tuple2<? extends K, ? extends V>> f) {
        Objects.requireNonNull(f, "f is null");
        return ofEntries(Collections.tabulate(n, (Function<? super Integer, ? extends Tuple2<K, V>>) f));
    }

    @Override
    public <K2, V2> SequencedChampMap<K2, V2> bimap(Function<? super K, ? extends K2> keyMapper, Function<? super V, ? extends V2> valueMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        Objects.requireNonNull(valueMapper, "valueMapper is null");
        final io.vavr.collection.Iterator<Tuple2<K2, V2>> entries = iterator().map(entry -> Tuple.of(keyMapper.apply(entry._1), valueMapper.apply(entry._2)));
        return SequencedChampMap.ofEntries(entries);
    }

    @Override
    public Tuple2<V, SequencedChampMap<K, V>> computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        return Maps.computeIfAbsent(this, key, mappingFunction);
    }

    @Override
    public Tuple2<Option<V>, SequencedChampMap<K, V>> computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        return Maps.computeIfPresent(this, key, remappingFunction);
    }

    @Override
    public boolean containsKey(K key) {
        return root.find(new ChampSequenced.ChampSequencedEntry<>(key), ChampSequenced.ChampSequencedEntry.keyHash(key), 0,
                ChampSequenced.ChampSequencedEntry::keyEquals) != ChampTrie.Node.NO_DATA;
    }

    // We need this method to narrow the argument of `ofEntries`.
    // If this method is static with type args <K, V>, the jdk fails to infer types at the call site.
    private SequencedChampMap<K, V> createFromEntries(Iterable<Tuple2<K, V>> tuples) {
        return SequencedChampMap.ofEntries(tuples);
    }

    @Override
    public SequencedChampMap<K, V> distinct() {
        return Maps.distinct(this);
    }

    @Override
    public SequencedChampMap<K, V> distinctBy(Comparator<? super Tuple2<K, V>> comparator) {
        return Maps.distinctBy(this, this::createFromEntries, comparator);
    }

    @Override
    public <U> SequencedChampMap<K, V> distinctBy(Function<? super Tuple2<K, V>, ? extends U> keyExtractor) {
        return Maps.distinctBy(this, this::createFromEntries, keyExtractor);
    }

    @Override
    public SequencedChampMap<K, V> drop(int n) {
        return n <= 0 ? this : ofEntries(iterator(n));
    }

    @Override
    public SequencedChampMap<K, V> dropRight(int n) {
        return Maps.dropRight(this, this::createFromEntries, SequencedChampMap::empty, n);
    }

    @Override
    public SequencedChampMap<K, V> dropUntil(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.dropUntil(this, this::createFromEntries, predicate);
    }

    @Override
    public SequencedChampMap<K, V> dropWhile(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.dropWhile(this, this::createFromEntries, predicate);
    }

    @Override
    public boolean equals(Object o) {
        return Collections.equals(this, o);
    }

    @Override
    public SequencedChampMap<K, V> filter(BiPredicate<? super K, ? super V> predicate) {
        TransientLinkedHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(e.getKey(), e.getValue()));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public SequencedChampMap<K, V> filter(Predicate<? super Tuple2<K, V>> predicate) {
        TransientLinkedHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(new Tuple2<>(e.getKey(), e.getValue())));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public SequencedChampMap<K, V> filterKeys(Predicate<? super K> predicate) {
        TransientLinkedHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(e.getKey()));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public SequencedChampMap<K, V> filterValues(Predicate<? super V> predicate) {
        TransientLinkedHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(e.getValue()));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public <K2, V2> SequencedChampMap<K2, V2> flatMap(BiFunction<? super K, ? super V, ? extends Iterable<Tuple2<K2, V2>>> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        return foldLeft(SequencedChampMap.<K2, V2>empty(), (acc, entry) -> {
            for (Tuple2<? extends K2, ? extends V2> mappedEntry : mapper.apply(entry._1, entry._2)) {
                acc = acc.put(mappedEntry);
            }
            return acc;
        });
    }

    @SuppressWarnings("unchecked")
    @Override
    public Option<V> get(K key) {
        Object result = root.find(
                new ChampSequenced.ChampSequencedEntry<>(key),
                ChampSequenced.ChampSequencedEntry.keyHash(key), 0, ChampSequenced.ChampSequencedEntry::keyEquals);
        return ((result instanceof ChampSequenced.ChampSequencedEntry<?, ?>) ? Option.some((V) ((ChampSequenced.ChampSequencedEntry<?, ?>) result).getValue()) : Option.none());
    }

    @Override
    public V getOrElse(K key, V defaultValue) {
        return get(key).getOrElse(defaultValue);
    }

    @Override
    public <C> io.vavr.collection.Map<C, SequencedChampMap<K, V>> groupBy(Function<? super Tuple2<K, V>, ? extends C> classifier) {
        return Maps.groupBy(this, this::createFromEntries, classifier, empty());
    }

    @Override
    public io.vavr.collection.Iterator<SequencedChampMap<K, V>> grouped(int size) {
        return Maps.grouped(this, this::createFromEntries, size);
    }

    @Override
    public int hashCode() {
        return Collections.hashUnordered(this);
    }

    @SuppressWarnings("unchecked")
    @Override
    public Tuple2<K, V> head() {
        Map.Entry<K, V> entry = (Map.Entry<K, V>) vector.head();
        return new Tuple2<>(entry.getKey(), entry.getValue());
    }

    @Override
    public SequencedChampMap<K, V> init() {
        if (isEmpty()) {
            throw new UnsupportedOperationException("init of empty SequencedChampMap");
        }
        return remove(last()._1);
    }

    @Override
    public Option<SequencedChampMap<K, V>> initOption() {
        return Maps.initOption(this);
    }

    /**
     * An {@code SequencedChampMap}'s value is computed synchronously.
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
     * An {@code SequencedChampMap}'s value is computed eagerly.
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
    public io.vavr.collection.Iterator<Tuple2<K, V>> iterator() {
        return new ChampIteration.IteratorFacade<>(spliterator());
    }

    io.vavr.collection.Iterator<Tuple2<K, V>> iterator(int startIndex) {
        return new ChampIteration.IteratorFacade<>(spliterator(startIndex));
    }

    @Override
    public io.vavr.collection.Set<K> keySet() {
        return io.vavr.collection.LinkedHashSet.ofAll(iterator().map(Tuple2::_1));
    }

    @Override
    @SuppressWarnings("unchecked")
    public Tuple2<K, V> last() {
        Map.Entry<K, V> entry = (Map.Entry<K, V>) vector.last();
        return new Tuple2<>(entry.getKey(), entry.getValue());
    }

    @Override
    public <K2, V2> SequencedChampMap<K2, V2> map(BiFunction<? super K, ? super V, Tuple2<K2, V2>> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        return foldLeft(SequencedChampMap.empty(), (acc, entry) -> acc.put(entry.map(mapper)));
    }

    @Override
    public <K2> SequencedChampMap<K2, V> mapKeys(Function<? super K, ? extends K2> keyMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        return map((k, v) -> Tuple.of(keyMapper.apply(k), v));
    }

    @Override
    public <K2> SequencedChampMap<K2, V> mapKeys(Function<? super K, ? extends K2> keyMapper, BiFunction<? super V, ? super V, ? extends V> valueMerge) {
        return Collections.mapKeys(this, SequencedChampMap.empty(), keyMapper, valueMerge);
    }

    @Override
    public <W> SequencedChampMap<K, W> mapValues(Function<? super V, ? extends W> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        return map((k, v) -> Tuple.of(k, mapper.apply(v)));
    }

    @Override
    public SequencedChampMap<K, V> merge(io.vavr.collection.Map<? extends K, ? extends V> that) {
        return putAllTuples(that);
    }

    @Override
    public <U extends V> SequencedChampMap<K, V> merge(io.vavr.collection.Map<? extends K, U> that,
                                                       BiFunction<? super V, ? super U, ? extends V> collisionResolution) {
        return Maps.merge(this, this::createFromEntries, that, collisionResolution);
    }

    @Override
    public SequencedChampMap<K, V> orElse(Iterable<? extends Tuple2<K, V>> other) {
        return isEmpty() ? ofEntries(other) : this;
    }

    @Override
    public SequencedChampMap<K, V> orElse(Supplier<? extends Iterable<? extends Tuple2<K, V>>> supplier) {
        return isEmpty() ? ofEntries(supplier.get()) : this;
    }

    @Override
    public Tuple2<SequencedChampMap<K, V>, SequencedChampMap<K, V>> partition(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.partition(this, this::createFromEntries, predicate);
    }

    @Override
    public SequencedChampMap<K, V> peek(Consumer<? super Tuple2<K, V>> action) {
        return Maps.peek(this, action);
    }

    @Override
    public <U extends V> SequencedChampMap<K, V> put(K key, U value, BiFunction<? super V, ? super U, ? extends V> merge) {
        return Maps.put(this, key, value, merge);
    }

    /**
     * Associates the specified value with the specified key in this map.
     * If the map previously contained a mapping for the key, the old value is
     * replaced by the specified value.
     * <p>
     * Note that this method has a worst-case linear complexity.
     *
     * @param key   key with which the specified value is to be associated
     * @param value value to be associated with the specified key
     * @return A new Map containing these elements and that entry.
     */
    @Override
    public SequencedChampMap<K, V> put(K key, V value) {
        return putLast(key, value, false);
    }

    @Override
    public SequencedChampMap<K, V> put(Tuple2<? extends K, ? extends V> entry) {
        return Maps.put(this, entry);
    }

    @Override
    public <U extends V> SequencedChampMap<K, V> put(Tuple2<? extends K, U> entry,
                                                     BiFunction<? super V, ? super U, ? extends V> merge) {
        return Maps.put(this, entry, merge);
    }

    private SequencedChampMap<K, V> putAllEntries(Iterable<? extends Map.Entry<? extends K, ? extends V>> c) {
        TransientLinkedHashMap<K, V> t = toTransient();
        t.putAllEntries(c);
        return t.root == this.root ? this : t.toImmutable();
    }

    @SuppressWarnings("unchecked")
    private SequencedChampMap<K, V> putAllTuples(Iterable<? extends Tuple2<? extends K, ? extends V>> c) {
        if (isEmpty() && c instanceof SequencedChampMap<?, ?>) {
            SequencedChampMap<?, ?> that = (SequencedChampMap<?, ?>) c;
            return (SequencedChampMap<K, V>) that;
        }
        TransientLinkedHashMap<K, V> t = toTransient();
        t.putAllTuples(c);
        return t.root == this.root ? this : t.toImmutable();
    }

    private SequencedChampMap<K, V> putLast(K key, V value, boolean moveToLast) {
        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>>();
        ChampSequenced.ChampSequencedEntry<K, V> newEntry = new ChampSequenced.ChampSequencedEntry<>(key, value, vector.size() - offset);
        ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>> newRoot = root.put(null, newEntry,
                ChampSequenced.ChampSequencedEntry.keyHash(key), 0, details,
                moveToLast ? ChampSequenced.ChampSequencedEntry::updateAndMoveToLast : ChampSequenced.ChampSequencedEntry::updateWithNewKey,
                ChampSequenced.ChampSequencedEntry::keyEquals, ChampSequenced.ChampSequencedEntry::entryKeyHash);
        if (details.isReplaced()
                && details.getOldDataNonNull().getSequenceNumber() == details.getNewDataNonNull().getSequenceNumber()) {
            BitMappedTrie<Object> newVector = vector.update(details.getNewDataNonNull().getSequenceNumber() - offset, details.getNewDataNonNull());
            return new SequencedChampMap<>(newRoot, newVector, size, offset);
        }
        if (details.isModified()) {
            BitMappedTrie<Object> newVector = vector;
            int newOffset = offset;
            int newSize = size;
            if (details.isReplaced()) {
                if (moveToLast) {
                    ChampSequenced.ChampSequencedEntry<K, V> oldElem = details.getOldDataNonNull();
                    Tuple2<BitMappedTrie<Object>, Integer> result = ChampSequenced.ChampSequencedData.vecRemove(newVector, oldElem, newOffset);
                    newVector = result._1;
                    newOffset = result._2;
                }
            } else {
                newSize++;
            }
            newVector = newVector.append(newEntry);
            return renumber(newRoot, newVector, newSize, newOffset);
        }
        return this;
    }

    private Object readResolve() {
        return isEmpty() ? EMPTY : this;
    }

    public SequencedChampMap<K, V> reject(Predicate<? super Tuple2<K, V>> predicate) {
        return (SequencedChampMap) Maps.reject(this, this::createFromEntries, predicate);
    }

    public SequencedChampMap<K, V> reject(BiPredicate<? super K, ? super V> predicate) {
        return (SequencedChampMap) Maps.reject(this, this::createFromEntries, predicate);
    }

    public SequencedChampMap<K, V> rejectKeys(Predicate<? super K> predicate) {
        return (SequencedChampMap) Maps.rejectKeys(this, this::createFromEntries, predicate);
    }

    public SequencedChampMap<K, V> rejectValues(Predicate<? super V> predicate) {
        return (SequencedChampMap) Maps.rejectValues(this, this::createFromEntries, predicate);
    }

    @Override
    public SequencedChampMap<K, V> remove(K key) {
        int keyHash = ChampSequenced.ChampSequencedEntry.keyHash(key);
        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>>();
        ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>> newRoot = root.remove(null,
                new ChampSequenced.ChampSequencedEntry<>(key),
                keyHash, 0, details, ChampSequenced.ChampSequencedEntry::keyEquals);
        if (details.isModified()) {
            ChampSequenced.ChampSequencedEntry<K, V> oldElem = details.getOldDataNonNull();
            Tuple2<BitMappedTrie<Object>, Integer> result = ChampSequenced.ChampSequencedData.vecRemove(vector, oldElem, offset);
            return renumber(newRoot, result._1, size - 1, result._2);
        }
        return this;
    }

    @Override
    public SequencedChampMap<K, V> removeAll(BiPredicate<? super K, ? super V> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.reject(predicate);
    }

    @Override
    public SequencedChampMap<K, V> removeAll(Iterable<? extends K> keys) {
        Objects.requireNonNull(keys, "keys is null");
        TransientLinkedHashMap<K, V> t = toTransient();
        return t.removeAll(keys) ? t.toImmutable() : this;
    }

    @Override
    public SequencedChampMap<K, V> removeKeys(Predicate<? super K> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.rejectKeys(predicate);
    }

    @Override
    public SequencedChampMap<K, V> removeValues(Predicate<? super V> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.rejectValues(predicate);
    }

    private SequencedChampMap<K, V> renumber(
            ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>> root,
            BitMappedTrie<Object> vector,
            int size, int offset) {

        if (ChampSequenced.ChampSequencedData.vecMustRenumber(size, offset, this.vector.size())) {
            ChampTrie.IdentityObject owner = new ChampTrie.IdentityObject();
            Tuple2<ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>>, BitMappedTrie<Object>> result = ChampSequenced.ChampSequencedData.<ChampSequenced.ChampSequencedEntry<K, V>>vecRenumber(
                    size, root, vector, owner, ChampSequenced.ChampSequencedEntry::entryKeyHash, ChampSequenced.ChampSequencedEntry::keyEquals,
                    (e, seq) -> new ChampSequenced.ChampSequencedEntry<>(e.getKey(), e.getValue(), seq));
            return new SequencedChampMap<>(
                    result._1, result._2,
                    size, 0);
        }
        return new SequencedChampMap<>(root, vector, size, offset);
    }

    @Override
    public SequencedChampMap<K, V> replace(Tuple2<K, V> currentEntry, Tuple2<K, V> newEntry) {
        // currentEntry and newEntry are the same => do nothing
        if (Objects.equals(currentEntry, newEntry)) {
            return this;
        }

        // try to remove currentEntry from the 'root' trie
        final ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> detailsCurrent = new ChampTrie.ChangeEvent<>();
        ChampTrie.IdentityObject owner = new ChampTrie.IdentityObject();
        ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>> newRoot = root.remove(owner,
                new ChampSequenced.ChampSequencedEntry<K, V>(currentEntry._1, currentEntry._2),
                Objects.hashCode(currentEntry._1), 0, detailsCurrent, ChampSequenced.ChampSequencedEntry::keyAndValueEquals);
        // currentElement was not in the 'root' trie => do nothing
        if (!detailsCurrent.isModified()) {
            return this;
        }

        // removedData was in the 'root' trie, and we have just removed it
        // => also remove its entry from the 'sequenceRoot' trie
        BitMappedTrie<Object> newVector = vector;
        int newOffset = offset;
        ChampSequenced.ChampSequencedEntry<K, V> removedData = detailsCurrent.getOldData();
        int seq = removedData.getSequenceNumber();
        Tuple2<BitMappedTrie<Object>, Integer> result = ChampSequenced.ChampSequencedData.vecRemove(newVector, removedData, offset);
        newVector = result._1;
        newOffset = result._2;

        // try to update the trie with the newData
        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> detailsNew = new ChampTrie.ChangeEvent<>();
        ChampSequenced.ChampSequencedEntry<K, V> newData = new ChampSequenced.ChampSequencedEntry<>(newEntry._1, newEntry._2, seq);
        newRoot = newRoot.put(owner,
                newData, Objects.hashCode(newEntry._1), 0, detailsNew,
                ChampSequenced.ChampSequencedEntry::forceUpdate,
                ChampSequenced.ChampSequencedEntry::keyEquals, ChampSequenced.ChampSequencedEntry::entryKeyHash);
        boolean isReplaced = detailsNew.isReplaced();

        // there already was data with key newData.getKey() in the trie, and we have just replaced it
        // => remove the replaced data from the vector
        if (isReplaced) {
            ChampSequenced.ChampSequencedEntry<K, V> replacedData = detailsNew.getOldData();
            result = ChampSequenced.ChampSequencedData.vecRemove(newVector, replacedData, newOffset);
            newVector = result._1;
            newOffset = result._2;
        }

        // we have just successfully added or replaced the newData
        // => insert the newData in the vector
        newVector = seq + newOffset < newVector.size() ? newVector.update(seq + newOffset, newData) : newVector.append(newData);

        if (isReplaced) {
            // we reduced the size of the map by one => renumbering may be necessary
            return renumber(newRoot, newVector, size - 1, newOffset);
        } else {
            // we did not change the size of the map => no renumbering is needed
            return new SequencedChampMap<>(newRoot, newVector, size, newOffset);
        }
    }

    @Override
    public SequencedChampMap<K, V> replace(K key, V oldValue, V newValue) {
        return Maps.replace(this, key, oldValue, newValue);
    }

    @Override
    public SequencedChampMap<K, V> replaceAll(Tuple2<K, V> currentElement, Tuple2<K, V> newElement) {
        return Maps.replaceAll(this, currentElement, newElement);
    }

    @Override
    public SequencedChampMap<K, V> replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        return Maps.replaceAll(this, function);
    }

    @Override
    public SequencedChampMap<K, V> replaceValue(K key, V value) {
        return Maps.replaceValue(this, key, value);
    }

    @Override
    public SequencedChampMap<K, V> retainAll(Iterable<? extends Tuple2<K, V>> elements) {
        TransientLinkedHashMap<K, V> t = toTransient();
        t.retainAllTuples(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    io.vavr.collection.Iterator<Tuple2<K, V>> reverseIterator() {
        return new ChampIteration.IteratorFacade<>(reverseSpliterator());
    }

    @SuppressWarnings("unchecked")
    Spliterator<Tuple2<K, V>> reverseSpliterator() {
        return new ChampSequenced.ChampReverseVectorSpliterator<>(vector,
                e -> new Tuple2<K, V>(((Map.Entry<K, V>) e).getKey(), ((Map.Entry<K, V>) e).getValue()),
                0, size(), Spliterator.SIZED | Spliterator.DISTINCT | Spliterator.ORDERED | Spliterator.IMMUTABLE);
    }

    @Override
    public SequencedChampMap<K, V> scan(
            Tuple2<K, V> zero,
            BiFunction<? super Tuple2<K, V>, ? super Tuple2<K, V>, ? extends Tuple2<K, V>> operation) {
        return Maps.scan(this, zero, operation, this::createFromEntries);
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public io.vavr.collection.Iterator<SequencedChampMap<K, V>> slideBy(Function<? super Tuple2<K, V>, ?> classifier) {
        return Maps.slideBy(this, this::createFromEntries, classifier);
    }

    @Override
    public io.vavr.collection.Iterator<SequencedChampMap<K, V>> sliding(int size) {
        return Maps.sliding(this, this::createFromEntries, size);
    }

    @Override
    public io.vavr.collection.Iterator<SequencedChampMap<K, V>> sliding(int size, int step) {
        return Maps.sliding(this, this::createFromEntries, size, step);
    }

    @Override
    public Tuple2<SequencedChampMap<K, V>, SequencedChampMap<K, V>> span(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.span(this, this::createFromEntries, predicate);
    }

    @SuppressWarnings("unchecked")
    @Override
    public Spliterator<Tuple2<K, V>> spliterator() {
        return spliterator(0);
    }

    @SuppressWarnings("unchecked")
    Spliterator<Tuple2<K, V>> spliterator(int startIndex) {
        return new ChampSequenced.ChampVectorSpliterator<>(vector,
                e -> new Tuple2<K, V>(((Map.Entry<K, V>) e).getKey(), ((Map.Entry<K, V>) e).getValue()),
                startIndex, size(), Spliterator.SIZED | Spliterator.DISTINCT | Spliterator.ORDERED | Spliterator.IMMUTABLE);
    }

    @Override
    public String stringPrefix() {
        return "SequencedChampMap";
    }

    @Override
    public SequencedChampMap<K, V> tail() {
        if (isEmpty()) {
            throw new UnsupportedOperationException("tail of empty SequencedChampMap");
        }
        return remove(head()._1);
    }

    @Override
    public Option<SequencedChampMap<K, V>> tailOption() {
        return Maps.tailOption(this);
    }

    @Override
    public SequencedChampMap<K, V> take(int n) {
        return Maps.take(this, this::createFromEntries, n);
    }

    @Override
    public SequencedChampMap<K, V> takeRight(int n) {
        return Maps.takeRight(this, this::createFromEntries, n);
    }

    @Override
    public SequencedChampMap<K, V> takeUntil(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.takeUntil(this, this::createFromEntries, predicate);
    }

    @Override
    public SequencedChampMap<K, V> takeWhile(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.takeWhile(this, this::createFromEntries, predicate);
    }

    @Override
    public java.util.LinkedHashMap<K, V> toJavaMap() {
        return toJavaMap(java.util.LinkedHashMap::new, t -> t);
    }

    @Override
    public String toString() {
        return mkString(stringPrefix() + "(", ", ", ")");
    }

    TransientLinkedHashMap<K, V> toTransient() {
        return new TransientLinkedHashMap<>(this);
    }

    @Override
    public Seq<V> values() {
        return map(t -> t._2);
    }

    private Object writeReplace() throws ObjectStreamException {
        return new SerializationProxy<>(this);
    }

    /**
     * A serialization proxy which, in this context, is used to deserialize immutable, linked Lists with final
     * instance fields.
     *
     * @param <K> The key type
     * @param <V> The value type
     */
    // DEV NOTE: The serialization proxy pattern is not compatible with non-final, i.e. extendable,
    // classes. Also, it may not be compatible with circular object graphs.
    private static final class SerializationProxy<K, V> implements Serializable {

        private static final long serialVersionUID = 1L;

        // the instance to be serialized/deserialized
        private transient SequencedChampMap<K, V> map;

        /**
         * Constructor for the case of serialization, called by {@link SequencedChampMap#writeReplace()}.
         * <p/>
         * The constructor of a SerializationProxy takes an argument that concisely represents the logical state of
         * an instance of the enclosing class.
         *
         * @param map a map
         */
        SerializationProxy(SequencedChampMap<K, V> map) {
            this.map = map;
        }

        /**
         * Read an object from a deserialization stream.
         *
         * @param s An object deserialization stream.
         * @throws ClassNotFoundException If the object's class read from the stream cannot be found.
         * @throws InvalidObjectException If the stream contains no list elements.
         * @throws IOException            If an error occurs reading from the stream.
         */
        @SuppressWarnings("unchecked")
        private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
            s.defaultReadObject();
            final int size = s.readInt();
            if (size < 0) {
                throw new InvalidObjectException("No elements");
            }
            TransientLinkedHashMap<K, V> t = new TransientLinkedHashMap<>();
            for (int i = 0; i < size; i++) {
                final K key = (K) s.readObject();
                final V value = (V) s.readObject();
                t.put(key, value);
            }
            map = t.toImmutable();
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
            return map;
        }

        /**
         * Write an object to a serialization stream.
         *
         * @param s An object serialization stream.
         * @throws IOException If an error occurs writing to the stream.
         */
        private void writeObject(ObjectOutputStream s) throws IOException {
            s.defaultWriteObject();
            s.writeInt(map.size());
            for (Tuple2<K, V> e : map) {
                s.writeObject(e._1);
                s.writeObject(e._2);
            }
        }
    }

    /**
     * Supports efficient bulk-operations on a linked hash map through transience.
     *
     * @param <K>the key type
     * @param <V>the value type
     */
    static class TransientLinkedHashMap<K, V> extends ChampTransience.ChampAbstractTransientMap<K, V, ChampSequenced.ChampSequencedEntry<K, V>> {
        /**
         * Offset of sequence numbers to vector indices.
         *
         * <pre>vector index = sequence number + offset</pre>
         */
        private int offset;
        /**
         * In this vector we store the elements in the order in which they were inserted.
         */
        private BitMappedTrie<Object> vector;

        TransientLinkedHashMap(SequencedChampMap<K, V> m) {
            vector = m.vector;
            root = m.root;
            offset = m.offset;
            size = m.size;
        }

        TransientLinkedHashMap() {
            this(empty());
        }

        @Override
        void clear() {
            root = emptyNode();
            vector = BitMappedTrie.empty();
            offset = 0;
            size = 0;
        }

        boolean filterAll(Predicate<Map.Entry<K, V>> predicate) {
            ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
            VectorSideEffectPredicate<K, V> vp = new VectorSideEffectPredicate<>(predicate, vector, offset);
            ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>> newRootNode = root.filterAll(makeOwner(), vp, 0, bulkChange);
            if (bulkChange.removed == 0) {
                return false;
            }
            root = newRootNode;
            vector = vp.newVector;
            offset = vector.isEmpty() ? 0 : vp.newOffset;
            size -= bulkChange.removed;
            modCount++;
            return true;
        }

        public V put(K key, V value) {
            ChampSequenced.ChampSequencedEntry<K, V> oldData = putLast(key, value, false).getOldData();
            return oldData == null ? null : oldData.getValue();
        }

        boolean putAllEntries(Iterable<? extends Map.Entry<? extends K, ? extends V>> c) {
            if (c == this) {
                return false;
            }
            boolean modified = false;
            for (Map.Entry<? extends K, ? extends V> e : c) {
                modified |= putLast(e.getKey(), e.getValue(), false).isModified();
            }
            return modified;
        }

        boolean putAllTuples(Iterable<? extends Tuple2<? extends K, ? extends V>> c) {
            if (c == this) {
                return false;
            }
            boolean modified = false;
            for (Tuple2<? extends K, ? extends V> e : c) {
                modified |= putLast(e._1, e._2, false).isModified();
            }
            return modified;
        }

        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> putLast(final K key, V value, boolean moveToLast) {
            ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>>();
            ChampSequenced.ChampSequencedEntry<K, V> newEntry = new ChampSequenced.ChampSequencedEntry<>(key, value, vector.size() - offset);
            ChampTrie.IdentityObject owner = makeOwner();
            root = root.put(owner, newEntry,
                    Objects.hashCode(key), 0, details,
                    moveToLast ? ChampSequenced.ChampSequencedEntry::updateAndMoveToLast : ChampSequenced.ChampSequencedEntry::updateWithNewKey,
                    ChampSequenced.ChampSequencedEntry::keyEquals, ChampSequenced.ChampSequencedEntry::entryKeyHash);
            if (details.isReplaced()
                    && details.getOldDataNonNull().getSequenceNumber() == details.getNewDataNonNull().getSequenceNumber()) {
                vector = vector.update(details.getNewDataNonNull().getSequenceNumber() - offset, details.getNewDataNonNull());
                return details;
            }
            if (details.isModified()) {
                if (details.isReplaced()) {
                    Tuple2<BitMappedTrie<Object>, Integer> result = ChampSequenced.ChampSequencedData.vecRemove(vector, details.getOldDataNonNull(), offset);
                    vector = result._1;
                    offset = result._2;
                } else {
                    size++;
                }
                modCount++;
                vector = vector.append(newEntry);
                renumber();
            }
            return details;
        }

        @SuppressWarnings("unchecked")
        boolean removeAll(Iterable<?> c) {
            if (isEmpty()) {
                return false;
            }
            boolean modified = false;
            for (Object key : c) {
                ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> details = removeKey((K) key);
                modified |= details.isModified();
            }
            return modified;
        }

        ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> removeKey(K key) {
            ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>> details = new ChampTrie.ChangeEvent<ChampSequenced.ChampSequencedEntry<K, V>>();
            root = root.remove(null,
                    new ChampSequenced.ChampSequencedEntry<>(key),
                    Objects.hashCode(key), 0, details, ChampSequenced.ChampSequencedEntry::keyEquals);
            if (details.isModified()) {
                ChampSequenced.ChampSequencedEntry<K, V> oldElem = details.getOldDataNonNull();
                Tuple2<BitMappedTrie<Object>, Integer> result = ChampSequenced.ChampSequencedData.vecRemove(vector, oldElem, offset);
                vector = result._1;
                offset = result._2;
                size--;
                modCount++;
                renumber();
            }
            return details;
        }

        void renumber() {
            if (ChampSequenced.ChampSequencedData.vecMustRenumber(size, offset, vector.size())) {
                ChampTrie.IdentityObject owner = makeOwner();
                Tuple2<ChampTrie.BitmapIndexedNode<ChampSequenced.ChampSequencedEntry<K, V>>, BitMappedTrie<Object>> result = ChampSequenced.ChampSequencedData.vecRenumber(size, root, vector, owner,
                        ChampSequenced.ChampSequencedEntry::entryKeyHash, ChampSequenced.ChampSequencedEntry::keyEquals,
                        (e, seq) -> new ChampSequenced.ChampSequencedEntry<>(e.getKey(), e.getValue(), seq));
                root = result._1;
                vector = result._2;
                offset = 0;
            }
        }

        public SequencedChampMap<K, V> toImmutable() {
            owner = null;
            return isEmpty()
                    ? empty()
                    : new SequencedChampMap<>(root, vector, size, offset);
        }

        static class VectorSideEffectPredicate<K, V> implements Predicate<ChampSequenced.ChampSequencedEntry<K, V>> {
            BitMappedTrie<Object> newVector;
            int newOffset;
            Predicate<? super Map.Entry<K, V>> predicate;

            public VectorSideEffectPredicate(Predicate<? super Map.Entry<K, V>> predicate, BitMappedTrie<Object> vector, int offset) {
                this.predicate = predicate;
                this.newVector = vector;
                this.newOffset = offset;
            }

            @Override
            public boolean test(ChampSequenced.ChampSequencedEntry<K, V> e) {
                if (!predicate.test(e)) {
                    Tuple2<BitMappedTrie<Object>, Integer> result = vecRemove(newVector, e, newOffset);
                    newVector = result._1;
                    newOffset = result._2;
                    return false;
                }
                return true;
            }
        }
    }

    @Override
    public Set<Tuple2<K, V>> toSet() {
        return (io.vavr.collection.Set) ValueModule.toTraversable(this, ChampSet.empty(), ChampSet::of, ChampSet::ofAll);
    }

    @Override
    public Set<Tuple2<K, V>> toLinkedSet() {
        return (io.vavr.collection.Set) ValueModule.toTraversable(this, SequencedChampSet.empty(), SequencedChampSet::of, SequencedChampSet::ofAll);
    }

}
