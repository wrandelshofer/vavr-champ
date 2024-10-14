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
import io.vavr.collection.Set;
import io.vavr.collection.Stream;
import io.vavr.collection.Traversable;
import io.vavr.control.Option;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Spliterator;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collector;

import static ch.randelshofer.vavr.champ.ChampTrie.BitmapIndexedNode.emptyNode;

/**
 * Implements an immutable map using a Compressed Hash-Array Mapped Prefix-tree
 * (CHAMP).
 * <p>
 * Features:
 * <ul>
 *     <li>supports up to 2<sup>30</sup> entries</li>
 *     <li>allows null keys and null values</li>
 *     <li>is immutable</li>
 *     <li>is thread-safe</li>
 *     <li>does not guarantee a specific iteration order</li>
 * </ul>
 * <p>
 * Performance characteristics:
 * <ul>
 *     <li>put: O(1)</li>
 *     <li>remove: O(1)</li>
 *     <li>containsKey: O(1)</li>
 *     <li>toMutable: O(1) + O(log N) distributed across subsequent updates in the mutable copy</li>
 *     <li>clone: O(1)</li>
 *     <li>iterator.next(): O(1)</li>
 * </ul>
 * <p>
 * Implementation details:
 * <p>
 * This map performs read and write operations of single elements in O(1) time,
 * and in O(1) space.
 * <p>
 * The CHAMP trie contains nodes that may be shared with other maps.
 * <p>
 * If a write operation is performed on a node, then this map creates a
 * copy of the node and of all parent nodes up to the root (copy-path-on-write).
 * Since the CHAMP trie has a fixed maximal height, the cost is O(1).
 * <p>
 * All operations on this map can be performed concurrently, without a need for
 * synchronisation.
 * <p>
 * The immutable version of this map extends from the non-public class
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
 * @param <K> the key type
 * @param <V> the value type
 */
public class ChampMap<K, V> implements io.vavr.collection.Map<K, V>, Serializable {
    /**
     * We do not guarantee an iteration order. Make sure that nobody accidentally relies on it.
     * <p>
     * XXX HashSetTest requires a specific iteration order of ChampSet! Therefore, we can not use SALT here.
     */
    static final int SALT = 0;//new java.util.Random().nextInt();
    private static final long serialVersionUID = 1L;

    private static final ChampMap<?, ?> EMPTY = new ChampMap<>(emptyNode(), 0);
    /**
     * The size of the map.
     */
    final int size;
    private final ChampTrie.BitmapIndexedNode<java.util.AbstractMap.SimpleImmutableEntry<K, V>> root;

    ChampMap(ChampTrie.BitmapIndexedNode<java.util.AbstractMap.SimpleImmutableEntry<K, V>> root, int size) {
        this.root = root;
        this.size = size;
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link ChampMap}.
     *
     * @param <K> The key type
     * @param <V> The value type
     * @return A {@link ChampMap} Collector.
     */
    public static <K, V> Collector<Tuple2<K, V>, ArrayList<Tuple2<K, V>>, ChampMap<K, V>> collector() {
        return Collections.toListAndThen(ChampMap::ofEntries);
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link ChampMap}.
     *
     * @param keyMapper The key mapper
     * @param <K>       The key type
     * @param <V>       The value type
     * @param <T>       Initial {@link java.util.stream.Stream} elements type
     * @return A {@link ChampMap} Collector.
     */
    public static <K, V, T extends V> Collector<T, ArrayList<T>, ChampMap<K, V>> collector(Function<? super T, ? extends K> keyMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        return ChampMap.collector(keyMapper, v -> v);
    }

    /**
     * Returns a {@link Collector} which may be used in conjunction with
     * {@link java.util.stream.Stream#collect(Collector)} to obtain a {@link ChampMap}.
     *
     * @param keyMapper   The key mapper
     * @param valueMapper The value mapper
     * @param <K>         The key type
     * @param <V>         The value type
     * @param <T>         Initial {@link java.util.stream.Stream} elements type
     * @return A {@link ChampMap} Collector.
     */
    public static <K, V, T> Collector<T, ArrayList<T>, ChampMap<K, V>> collector(
            Function<? super T, ? extends K> keyMapper, Function<? super T, ? extends V> valueMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        Objects.requireNonNull(valueMapper, "valueMapper is null");
        return Collections.toListAndThen(arr -> ChampMap.ofEntries(io.vavr.collection.Iterator.ofAll(arr)
                .map(t -> Tuple.of(keyMapper.apply(t), valueMapper.apply(t)))));
    }

    @SuppressWarnings("unchecked")
    public static <K, V> ChampMap<K, V> empty() {
        return (ChampMap<K, V>) EMPTY;
    }

    static <V, K> boolean entryKeyEquals(java.util.AbstractMap.SimpleImmutableEntry<K, V> a, java.util.AbstractMap.SimpleImmutableEntry<K, V> b) {
        return Objects.equals(a.getKey(), b.getKey());
    }

    static <V, K> int entryKeyHash(java.util.AbstractMap.SimpleImmutableEntry<K, V> e) {
        return SALT ^ Objects.hashCode(e.getKey());
    }

    /**
     * Returns a ChampMap containing tuples returned by {@code n} calls to a given Supplier {@code s}.
     *
     * @param <K> The key type
     * @param <V> The value type
     * @param n   The number of elements in the ChampMap
     * @param s   The Supplier computing element values
     * @return An ChampMap of size {@code n}, where each element contains the result supplied by {@code s}.
     * @throws NullPointerException if {@code s} is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> ChampMap<K, V> fill(int n, Supplier<? extends Tuple2<? extends K, ? extends V>> s) {
        Objects.requireNonNull(s, "s is null");
        return ofEntries(Collections.fill(n, (Supplier<? extends Tuple2<K, V>>) s));
    }

    static <V, K> boolean keyEquals(java.util.AbstractMap.SimpleImmutableEntry<K, V> a, java.util.AbstractMap.SimpleImmutableEntry<K, V> b) {
        return Objects.equals(a.getKey(), b.getKey());
    }

    static <V, K> int keyHash(Object e) {
        return SALT ^ Objects.hashCode(e);
    }

    /**
     * Narrows a widened {@code ChampMap<? extends K, ? extends V>} to {@code ChampMap<K, V>}
     * by performing a type-safe cast. This is eligible because immutable/read-only
     * collections are covariant.
     *
     * @param hashMap A {@code ChampMap}.
     * @param <K>     Key type
     * @param <V>     Value type
     * @return the given {@code hashMap} instance as narrowed type {@code ChampMap<K, V>}.
     */
    @SuppressWarnings("unchecked")
    public static <K, V> ChampMap<K, V> narrow(ChampMap<? extends K, ? extends V> hashMap) {
        return (ChampMap<K, V>) hashMap;
    }

    /**
     * Returns a singleton {@code ChampMap}, i.e. a {@code ChampMap} of one element.
     *
     * @param entry A map entry.
     * @param <K>   The key type
     * @param <V>   The value type
     * @return A new Map containing the given entry
     */
    public static <K, V> ChampMap<K, V> of(Tuple2<? extends K, ? extends V> entry) {
        return ChampMap.<K, V>empty().put(entry._1, entry._2);
    }

    /**
     * Returns a singleton {@code ChampMap}, i.e. a {@code ChampMap} of one element.
     *
     * @param key   A singleton map key.
     * @param value A singleton map value.
     * @param <K>   The key type
     * @param <V>   The value type
     * @return A new Map containing the given entry
     */
    public static <K, V> ChampMap<K, V> of(K key, V value) {
        return ChampMap.<K, V>empty().put(key, value);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
     *
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2) {
        return of(k1, v1).put(k2, v2);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
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
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3) {
        return of(k1, v1, k2, v2).put(k3, v3);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
     *
     * @param <K> The key type
     * @param <V> The value type
     * @param k1  a key for the map
     * @param v1  the value for k1
     * @param k2  a key for the map
     * @param v2  the value for k2
     * @param k3  a key for the map
     * @param v3  the value for k3
     * @param k4  a key for the map
     * @param v4  the value for k4
     * @return A new Map containing the given entries
     */
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4) {
        return of(k1, v1, k2, v2, k3, v3).put(k4, v4);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
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
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5) {
        return of(k1, v1, k2, v2, k3, v3, k4, v4).put(k5, v5);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
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
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6) {
        return of(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5).put(k6, v6);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
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
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7) {
        return of(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6).put(k7, v7);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
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
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8) {
        return of(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6, k7, v7).put(k8, v8);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
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
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8, K k9, V v9) {
        return of(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6, k7, v7, k8, v8).put(k9, v9);
    }

    /**
     * Creates a ChampMap of the given list of key-value pairs.
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
    public static <K, V> ChampMap<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8, K k9, V v9, K k10, V v10) {
        return of(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6, k7, v7, k8, v8, k9, v9).put(k10, v10);
    }

    /**
     * Returns a {@code ChampMap}, from a source java.util.Map.
     *
     * @param map A map
     * @param <K> The key type
     * @param <V> The value type
     * @return A new Map containing the given map
     */
    public static <K, V> ChampMap<K, V> ofAll(Map<? extends K, ? extends V> map) {
        return ChampMap.<K, V>empty().putAllEntries(map.entrySet());
    }

    /**
     * Returns a {@code ChampMap}, from entries mapped from stream.
     *
     * @param stream      the source stream
     * @param keyMapper   the key mapper
     * @param valueMapper the value mapper
     * @param <T>         The stream element type
     * @param <K>         The key type
     * @param <V>         The value type
     * @return A new Map
     */
    public static <T, K, V> ChampMap<K, V> ofAll(java.util.stream.Stream<? extends T> stream,
                                                 Function<? super T, ? extends K> keyMapper,
                                                 Function<? super T, ? extends V> valueMapper) {
        return Maps.ofStream(empty(), stream, keyMapper, valueMapper);
    }

    /**
     * Returns a {@code ChampMap}, from entries mapped from stream.
     *
     * @param stream      the source stream
     * @param entryMapper the entry mapper
     * @param <T>         The stream element type
     * @param <K>         The key type
     * @param <V>         The value type
     * @return A new Map
     */
    public static <T, K, V> ChampMap<K, V> ofAll(java.util.stream.Stream<? extends T> stream,
                                                 Function<? super T, Tuple2<? extends K, ? extends V>> entryMapper) {
        return Maps.ofStream(empty(), stream, entryMapper);
    }

    /**
     * Creates a ChampMap of the given entries.
     *
     * @param entries Map entries
     * @param <K>     The key type
     * @param <V>     The value type
     * @return A new Map containing the given entries
     */
    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <K, V> ChampMap<K, V> ofEntries(Map.Entry<? extends K, ? extends V>... entries) {
        Objects.requireNonNull(entries, "entries is null");
        return ChampMap.<K, V>empty().putAllEntries(Arrays.asList(entries));
    }

    /**
     * Creates a ChampMap of the given entries.
     *
     * @param entries Map entries
     * @param <K>     The key type
     * @param <V>     The value type
     * @return A new Map containing the given entries
     */
    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <K, V> ChampMap<K, V> ofEntries(Tuple2<? extends K, ? extends V>... entries) {
        Objects.requireNonNull(entries, "entries is null");
        return ChampMap.<K, V>empty().putAllTuples(Arrays.asList(entries));
    }

    /**
     * Creates a ChampMap of the given entries.
     *
     * @param entries Map entries
     * @param <K>     The key type
     * @param <V>     The value type
     * @return A new Map containing the given entries
     */
    public static <K, V> ChampMap<K, V> ofEntries(Iterable<? extends Tuple2<? extends K, ? extends V>> entries) {
        Objects.requireNonNull(entries, "entries is null");
        return ChampMap.<K, V>empty().putAllTuples(entries);
    }

    /**
     * Returns an ChampMap containing {@code n} values of a given Function {@code f}
     * over a range of integer values from 0 to {@code n - 1}.
     *
     * @param <K> The key type
     * @param <V> The value type
     * @param n   The number of elements in the ChampMap
     * @param f   The Function computing element values
     * @return An ChampMap consisting of elements {@code f(0),f(1), ..., f(n - 1)}
     * @throws NullPointerException if {@code f} is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> ChampMap<K, V> tabulate(int n, Function<? super Integer, ? extends Tuple2<? extends K, ? extends V>> f) {
        Objects.requireNonNull(f, "f is null");
        return ofEntries(Collections.tabulate(n, (Function<? super Integer, ? extends Tuple2<K, V>>) f));
    }

    static <K, V> java.util.AbstractMap.SimpleImmutableEntry<K, V> updateEntry(java.util.AbstractMap.SimpleImmutableEntry<K, V> oldv, java.util.AbstractMap.SimpleImmutableEntry<K, V> newv) {
        return Objects.equals(oldv.getValue(), newv.getValue()) ? oldv : newv;
    }

    // FIXME This behavior is enforced by AbstractMapTest.shouldPutExistingKeyAndNonEqualValue().<br>
    //     This behavior replaces the existing key with the new one if it has not the same identity.<br>
    //     This behavior does not match the behavior of java.util.ChampMap.put().
    //     This behavior violates the contract of the map: we do create a new instance of the map,
    //     although it is equal to the previous instance.
    static <K, V> java.util.AbstractMap.SimpleImmutableEntry<K, V> updateWithNewKey(java.util.AbstractMap.SimpleImmutableEntry<K, V> oldv, java.util.AbstractMap.SimpleImmutableEntry<K, V> newv) {
        return Objects.equals(oldv.getValue(), newv.getValue())
                && oldv.getKey() == newv.getKey()
                ? oldv
                : newv;
    }

    @Override
    public <K2, V2> ChampMap<K2, V2> bimap(Function<? super K, ? extends K2> keyMapper, Function<? super V, ? extends V2> valueMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        Objects.requireNonNull(valueMapper, "valueMapper is null");
        final io.vavr.collection.Iterator<Tuple2<K2, V2>> entries = iterator().map(entry -> Tuple.of(keyMapper.apply(entry._1), valueMapper.apply(entry._2)));
        return ChampMap.ofEntries(entries);
    }

    @Override
    public Tuple2<V, ChampMap<K, V>> computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        return Maps.computeIfAbsent(this, key, mappingFunction);
    }

    @Override
    public Tuple2<Option<V>, ChampMap<K, V>> computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        return Maps.computeIfPresent(this, key, remappingFunction);
    }

    @Override
    public boolean containsKey(K key) {
        return root.find(new java.util.AbstractMap.SimpleImmutableEntry<>(key, null), Objects.hashCode(key), 0,
                ChampMap::keyEquals) != ChampTrie.Node.NO_DATA;
    }

    // We need this method to narrow the argument of `ofEntries`.
    // If this method is static with type args <K, V>, the jdk fails to infer types at the call site.
    private ChampMap<K, V> createFromEntries(Iterable<Tuple2<K, V>> tuples) {
        return ChampMap.ofEntries(tuples);
    }

    @Override
    public ChampMap<K, V> distinct() {
        return Maps.distinct(this);
    }

    @Override
    public ChampMap<K, V> distinctBy(Comparator<? super Tuple2<K, V>> comparator) {
        return Maps.distinctBy(this, this::createFromEntries, comparator);
    }

    @Override
    public <U> ChampMap<K, V> distinctBy(Function<? super Tuple2<K, V>, ? extends U> keyExtractor) {
        return Maps.distinctBy(this, this::createFromEntries, keyExtractor);
    }

    @Override
    public ChampMap<K, V> drop(int n) {
        return Maps.drop(this, this::createFromEntries, ChampMap::empty, n);
    }

    @Override
    public ChampMap<K, V> dropRight(int n) {
        return Maps.dropRight(this, this::createFromEntries, ChampMap::empty, n);
    }

    @Override
    public ChampMap<K, V> dropUntil(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.dropUntil(this, this::createFromEntries, predicate);
    }

    @Override
    public ChampMap<K, V> dropWhile(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.dropWhile(this, this::createFromEntries, predicate);
    }

    @Override
    public boolean equals(final Object other) {
        if (other == this) {
            return true;
        }
        if (other == null) {
            return false;
        }
        if (other instanceof ChampMap) {
            ChampMap<?, ?> that = (ChampMap<?, ?>) other;
            return size == that.size && root.equivalent(that.root);
        } else {
            return Collections.equals(this, other);
        }
    }

    @Override
    public ChampMap<K, V> filter(BiPredicate<? super K, ? super V> predicate) {
        TransientHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(e.getKey(), e.getValue()));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public ChampMap<K, V> filter(Predicate<? super Tuple2<K, V>> predicate) {
        TransientHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(new Tuple2<>(e.getKey(), e.getValue())));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public ChampMap<K, V> filterKeys(Predicate<? super K> predicate) {
        TransientHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(e.getKey()));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public ChampMap<K, V> filterValues(Predicate<? super V> predicate) {
        TransientHashMap<K, V> t = toTransient();
        t.filterAll(e -> predicate.test(e.getValue()));
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public <K2, V2> ChampMap<K2, V2> flatMap(BiFunction<? super K, ? super V, ? extends Iterable<Tuple2<K2, V2>>> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        return foldLeft(ChampMap.<K2, V2>empty(), (acc, entry) -> {
            for (Tuple2<? extends K2, ? extends V2> mappedEntry : mapper.apply(entry._1, entry._2)) {
                acc = acc.put(mappedEntry);
            }
            return acc;
        });
    }

    @Override
    @SuppressWarnings("unchecked")
    public Option<V> get(K key) {
        Object result = root.find(new java.util.AbstractMap.SimpleImmutableEntry<>(key, null), Objects.hashCode(key), 0, ChampMap::keyEquals);
        return result == ChampTrie.Node.NO_DATA || result == null
                ? Option.none()
                : Option.some(((java.util.AbstractMap.SimpleImmutableEntry<K, V>) result).getValue());
    }

    @Override
    public V getOrElse(K key, V defaultValue) {
        return get(key).getOrElse(defaultValue);
    }

    @Override
    public <C> io.vavr.collection.Map<C, ChampMap<K, V>> groupBy(Function<? super Tuple2<K, V>, ? extends C> classifier) {
        return Maps.groupBy(this, this::createFromEntries, classifier, SequencedChampMap.empty());
    }

    @Override
    public io.vavr.collection.Iterator<ChampMap<K, V>> grouped(int size) {
        return Maps.grouped(this, this::createFromEntries, size);
    }

    @Override
    public int hashCode() {
        return Collections.hashUnordered(this);
    }

    @Override
    public Tuple2<K, V> head() {
        if (isEmpty()) {
            throw new NoSuchElementException("head of empty ChampMap");
        }
        java.util.AbstractMap.SimpleImmutableEntry<K, V> entry = ChampTrie.Node.getFirst(root);
        return new Tuple2<>(entry.getKey(), entry.getValue());
    }

    /**
     * XXX We return tail() here. I believe that this is correct.
     * See identical code in {@link io.vavr.collection.HashSet#init}
     */
    @Override
    public ChampMap<K, V> init() {
        if (isEmpty()) {
            throw new UnsupportedOperationException("tail of empty ChampMap");
        }
        return remove(last()._1);
    }

    @Override
    public Option<ChampMap<K, V>> initOption() {
        return Maps.initOption(this);
    }

    /**
     * A {@code ChampMap} is computed synchronously.
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
     * A {@code ChampMap} is computed eagerly.
     *
     * @return false
     */
    @Override
    public boolean isLazy() {
        return false;
    }

    @Override
    public io.vavr.collection.Iterator<Tuple2<K, V>> iterator() {
        return new ChampIteration.IteratorFacade<>(spliterator());
    }

    @Override
    public io.vavr.collection.Set<K> keySet() {
        return io.vavr.collection.HashSet.ofAll(iterator().map(Tuple2::_1));
    }

    @Override
    public io.vavr.collection.Iterator<K> keysIterator() {
        return new ChampIteration.IteratorFacade<>(keysSpliterator());
    }

    private Spliterator<K> keysSpliterator() {
        return new ChampIteration.ChampSpliterator<>(root, java.util.AbstractMap.SimpleImmutableEntry::getKey,
                Spliterator.DISTINCT | Spliterator.SIZED | Spliterator.SUBSIZED | Spliterator.IMMUTABLE, size);
    }

    @Override
    public Tuple2<K, V> last() {
        if (isEmpty()) {
            throw new NoSuchElementException("last of empty ChampMap");
        }
        java.util.AbstractMap.SimpleImmutableEntry<K, V> entry = ChampTrie.Node.getLast(root);
        return new Tuple2<>(entry.getKey(), entry.getValue());
    }

    @Override
    public <K2, V2> ChampMap<K2, V2> map(BiFunction<? super K, ? super V, Tuple2<K2, V2>> mapper) {
        Objects.requireNonNull(mapper, "mapper is null");
        return foldLeft(ChampMap.empty(), (acc, entry) -> acc.put(entry.map(mapper)));
    }

    @Override
    public <K2> ChampMap<K2, V> mapKeys(Function<? super K, ? extends K2> keyMapper) {
        Objects.requireNonNull(keyMapper, "keyMapper is null");
        return map((k, v) -> Tuple.of(keyMapper.apply(k), v));
    }

    @Override
    public <K2> ChampMap<K2, V> mapKeys(Function<? super K, ? extends K2> keyMapper, BiFunction<? super V, ? super V, ? extends V> valueMerge) {
        return Collections.mapKeys(this, ChampMap.empty(), keyMapper, valueMerge);
    }

    @Override
    public <V2> ChampMap<K, V2> mapValues(Function<? super V, ? extends V2> valueMapper) {
        Objects.requireNonNull(valueMapper, "valueMapper is null");
        return map((k, v) -> Tuple.of(k, valueMapper.apply(v)));
    }

    @Override
    public ChampMap<K, V> merge(io.vavr.collection.Map<? extends K, ? extends V> that) {
        return putAllTuples(that);
    }

    @Override
    public <U extends V> ChampMap<K, V> merge(io.vavr.collection.Map<? extends K, U> that,
                                              BiFunction<? super V, ? super U, ? extends V> collisionResolution) {
        return Maps.merge(this, this::createFromEntries, that, collisionResolution);
    }

    @Override
    public ChampMap<K, V> orElse(Iterable<? extends Tuple2<K, V>> other) {
        return isEmpty() ? ofEntries(other) : this;
    }

    @Override
    public ChampMap<K, V> orElse(Supplier<? extends Iterable<? extends Tuple2<K, V>>> supplier) {
        return isEmpty() ? ofEntries(supplier.get()) : this;
    }

    @Override
    public Tuple2<ChampMap<K, V>, ChampMap<K, V>> partition(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.partition(this, this::createFromEntries, predicate);
    }

    @Override
    public ChampMap<K, V> peek(Consumer<? super Tuple2<K, V>> action) {
        return Maps.peek(this, action);
    }

    @Override
    public <U extends V> ChampMap<K, V> put(K key, U value, BiFunction<? super V, ? super U, ? extends V> merge) {
        return Maps.put(this, key, value, merge);
    }

    @Override
    public ChampMap<K, V> put(K key, V value) {
        final ChampTrie.ChangeEvent<java.util.AbstractMap.SimpleImmutableEntry<K, V>> details = new ChampTrie.ChangeEvent<>();
        final ChampTrie.BitmapIndexedNode<java.util.AbstractMap.SimpleImmutableEntry<K, V>> newRootNode = root.put(null, new java.util.AbstractMap.SimpleImmutableEntry<>(key, value),
                Objects.hashCode(key), 0, details,
                ChampMap::updateWithNewKey, ChampMap::keyEquals, ChampMap::entryKeyHash);
        if (details.isModified()) {
            if (details.isReplaced()) {
                return new ChampMap<>(newRootNode, size);
            }
            return new ChampMap<>(newRootNode, size + 1);
        }
        return this;
    }

    @Override
    public ChampMap<K, V> put(Tuple2<? extends K, ? extends V> entry) {
        return Maps.put(this, entry);
    }

    @Override
    public <U extends V> ChampMap<K, V> put(Tuple2<? extends K, U> entry,
                                            BiFunction<? super V, ? super U, ? extends V> merge) {
        return Maps.put(this, entry, merge);
    }

    private ChampMap<K, V> putAllEntries(Iterable<? extends Map.Entry<? extends K, ? extends V>> c) {
        TransientHashMap<K, V> t = toTransient();
        t.putAllEntries(c);
        return t.root == this.root ? this : t.toImmutable();
    }

    @SuppressWarnings("unchecked")
    private ChampMap<K, V> putAllTuples(Iterable<? extends Tuple2<? extends K, ? extends V>> c) {
        if (isEmpty() && c instanceof ChampMap<?, ?>) {
            ChampMap<?, ?> that = (ChampMap<?, ?>) c;
            return (ChampMap<K, V>) that;
        }
        TransientHashMap<K, V> t = toTransient();
        t.putAllTuples(c);
        return t.root == this.root ? this : t.toImmutable();
    }

    private Object readResolve() {
        return isEmpty() ? EMPTY : this;
    }

    public ChampMap<K, V> reject(Predicate<? super Tuple2<K, V>> predicate) {
        return (ChampMap) Maps.reject(this, this::createFromEntries, predicate);
    }

    public ChampMap<K, V> reject(BiPredicate<? super K, ? super V> predicate) {
        return (ChampMap) Maps.reject(this, this::createFromEntries, predicate);
    }

    public ChampMap<K, V> rejectKeys(Predicate<? super K> predicate) {
        return (ChampMap) Maps.rejectKeys(this, this::createFromEntries, predicate);
    }

    public ChampMap<K, V> rejectValues(Predicate<? super V> predicate) {
        return (ChampMap) Maps.rejectValues(this, this::createFromEntries, predicate);
    }

    @Override
    public ChampMap<K, V> remove(K key) {
        final int keyHash = Objects.hashCode(key);
        final ChampTrie.ChangeEvent<java.util.AbstractMap.SimpleImmutableEntry<K, V>> details = new ChampTrie.ChangeEvent<>();
        final ChampTrie.BitmapIndexedNode<java.util.AbstractMap.SimpleImmutableEntry<K, V>> newRootNode =
                root.remove(null, new java.util.AbstractMap.SimpleImmutableEntry<>(key, null), keyHash, 0, details,
                        ChampMap::keyEquals);
        if (details.isModified()) {
            return new ChampMap<>(newRootNode, size - 1);
        }
        return this;
    }

    @Override
    public ChampMap<K, V> removeAll(BiPredicate<? super K, ? super V> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.reject(predicate);
    }

    @Override
    public ChampMap<K, V> removeAll(Iterable<? extends K> c) {
        TransientHashMap<K, V> t = toTransient();
        t.removeAll(c);
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public ChampMap<K, V> removeKeys(Predicate<? super K> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.rejectKeys(predicate);
    }

    @Override
    public ChampMap<K, V> removeValues(Predicate<? super V> predicate) {
        Objects.requireNonNull(predicate, "predicate is null");
        return this.rejectValues(predicate);
    }

    @Override
    public ChampMap<K, V> replace(Tuple2<K, V> currentElement, Tuple2<K, V> newElement) {
        return Maps.replace(this, currentElement, newElement);
    }

    @Override
    public ChampMap<K, V> replace(K key, V oldValue, V newValue) {
        return Maps.replace(this, key, oldValue, newValue);
    }

    @Override
    public ChampMap<K, V> replaceAll(Tuple2<K, V> currentElement, Tuple2<K, V> newElement) {
        return Maps.replaceAll(this, currentElement, newElement);
    }

    @Override
    public ChampMap<K, V> replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        return Maps.replaceAll(this, function);
    }

    @Override
    public ChampMap<K, V> replaceValue(K key, V value) {
        return Maps.replaceValue(this, key, value);
    }

    @Override
    public ChampMap<K, V> retainAll(Iterable<? extends Tuple2<K, V>> elements) {
        TransientHashMap<K, V> t = toTransient();
        t.retainAllTuples(elements);
        return t.root == this.root ? this : t.toImmutable();
    }

    @Override
    public ChampMap<K, V> scan(
            Tuple2<K, V> zero,
            BiFunction<? super Tuple2<K, V>, ? super Tuple2<K, V>, ? extends Tuple2<K, V>> operation) {
        return Maps.scan(this, zero, operation, this::createFromEntries);
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public io.vavr.collection.Iterator<ChampMap<K, V>> slideBy(Function<? super Tuple2<K, V>, ?> classifier) {
        return Maps.slideBy(this, this::createFromEntries, classifier);
    }

    @Override
    public io.vavr.collection.Iterator<ChampMap<K, V>> sliding(int size) {
        return Maps.sliding(this, this::createFromEntries, size);
    }

    @Override
    public io.vavr.collection.Iterator<ChampMap<K, V>> sliding(int size, int step) {
        return Maps.sliding(this, this::createFromEntries, size, step);
    }

    @Override
    public Tuple2<ChampMap<K, V>, ChampMap<K, V>> span(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.span(this, this::createFromEntries, predicate);
    }

    @Override
    public Spliterator<Tuple2<K, V>> spliterator() {
        return new ChampIteration.ChampSpliterator<>(root, entry -> new Tuple2<>(entry.getKey(), entry.getValue()),
                Spliterator.DISTINCT | Spliterator.SIZED | Spliterator.SUBSIZED | Spliterator.IMMUTABLE, size);
    }

    @Override
    public String stringPrefix() {
        return "ChampMap";
    }

    @Override
    public ChampMap<K, V> tail() {
        if (isEmpty()) {
            throw new UnsupportedOperationException("tail of empty ChampMap");
        }
        return remove(head()._1);
    }

    @Override
    public Option<ChampMap<K, V>> tailOption() {
        return Maps.tailOption(this);
    }

    @Override
    public ChampMap<K, V> take(int n) {
        return Maps.take(this, this::createFromEntries, n);
    }

    @Override
    public ChampMap<K, V> takeRight(int n) {
        return Maps.takeRight(this, this::createFromEntries, n);
    }

    @Override
    public ChampMap<K, V> takeUntil(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.takeUntil(this, this::createFromEntries, predicate);
    }

    @Override
    public ChampMap<K, V> takeWhile(Predicate<? super Tuple2<K, V>> predicate) {
        return Maps.takeWhile(this, this::createFromEntries, predicate);
    }

    @Override
    public java.util.HashMap<K, V> toJavaMap() {
        return toJavaMap(java.util.HashMap::new, t -> t);
    }

    @Override
    @SuppressWarnings("rawtypes")
    public io.vavr.collection.Map toLinkedMap(Function f) {
        Objects.requireNonNull(f, "f is null");
        Function<Tuple2<? extends K, ? extends V>, io.vavr.collection.Map<K, V>> ofElement = SequencedChampMap::of;
        Function<Iterable<Tuple2<? extends K, ? extends V>>, io.vavr.collection.Map<K, V>> ofAll = SequencedChampMap::ofEntries;
        return ValueModule.toMap(this, SequencedChampMap.empty(), ofElement, ofAll, f);
    }

    @Override
    public Set<Tuple2<K, V>> toLinkedSet() {
        return (io.vavr.collection.Set) ValueModule.toTraversable(this, SequencedChampSet.empty(), SequencedChampSet::of, SequencedChampSet::ofAll);
    }

    @Override
    @SuppressWarnings("rawtypes")
    public io.vavr.collection.Map toMap(Function f) {
        Objects.requireNonNull(f, "f is null");
        Function<Tuple2<? extends K, ? extends V>, io.vavr.collection.Map<K, V>> ofElement = ChampMap::of;
        Function<Iterable<Tuple2<? extends K, ? extends V>>, io.vavr.collection.Map<K, V>> ofAll = ChampMap::ofEntries;
        return ValueModule.toMap(this, ChampMap.empty(), ofElement, ofAll, f);
    }

    @Override
    public Set<Tuple2<K, V>> toSet() {
        return (io.vavr.collection.Set) ValueModule.toTraversable(this, ChampSet.empty(), ChampSet::of, ChampSet::ofAll);
    }

    @Override
    public String toString() {
        return mkString(stringPrefix() + "(", ", ", ")");
    }

    TransientHashMap<K, V> toTransient() {
        return new TransientHashMap<>(this);
    }

    @Override
    public Stream<V> values() {
        return valuesIterator().toStream();
    }

    @Override
    public io.vavr.collection.Iterator<V> valuesIterator() {
        return new ChampIteration.IteratorFacade<>(valuesSpliterator());
    }

    private Spliterator<V> valuesSpliterator() {
        return new ChampIteration.ChampSpliterator<>(root, java.util.AbstractMap.SimpleImmutableEntry::getValue,
                Spliterator.SIZED | Spliterator.SUBSIZED | Spliterator.IMMUTABLE, size);
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
        private transient ChampMap<K, V> map;

        /**
         * Constructor for the case of serialization, called by {@link ChampMap#writeReplace()}.
         * <p/>
         * The constructor of a SerializationProxy takes an argument that concisely represents the logical state of
         * an instance of the enclosing class.
         *
         * @param map a map
         */
        SerializationProxy(ChampMap<K, V> map) {
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
            ChampTrie.IdentityObject owner = new ChampTrie.IdentityObject();
            ChampTrie.BitmapIndexedNode<java.util.AbstractMap.SimpleImmutableEntry<K, V>> newRoot = emptyNode();
            ChampTrie.ChangeEvent<java.util.AbstractMap.SimpleImmutableEntry<K, V>> details = new ChampTrie.ChangeEvent<>();
            int newSize = 0;
            for (int i = 0; i < size; i++) {
                final K key = (K) s.readObject();
                final V value = (V) s.readObject();
                int keyHash = Objects.hashCode(key);
                newRoot = newRoot.put(owner, new java.util.AbstractMap.SimpleImmutableEntry<K, V>(key, value), keyHash, 0, details, ChampMap::updateEntry, Objects::equals, Objects::hashCode);
                if (details.isModified()) newSize++;
            }
            map = newSize == 0 ? empty() : new ChampMap<>(newRoot, newSize);
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
     * Supports efficient bulk-operations on a hash map through transience.
     *
     * @param <K>the key type
     * @param <V>the value type
     */
    static class TransientHashMap<K, V> extends ChampTransience.ChampAbstractTransientMap<K, V, java.util.AbstractMap.SimpleImmutableEntry<K, V>> {

        TransientHashMap(ChampMap<K, V> m) {
            root = m.root;
            size = m.size;
        }

        TransientHashMap() {
            this(empty());
        }

        @Override
        void clear() {
            root = emptyNode();
            size = 0;
            modCount++;
        }

        @SuppressWarnings("unchecked")
        boolean filterAll(Predicate<Map.Entry<K, V>> predicate) {
            ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
            ChampTrie.BitmapIndexedNode<AbstractMap.SimpleImmutableEntry<K, V>> newRootNode = root.filterAll(makeOwner(), predicate, 0, bulkChange);
            if (bulkChange.removed == 0) {
                return false;
            }
            root = newRootNode;
            size -= bulkChange.removed;
            modCount++;
            return true;
        }

        public V put(K key, V value) {
            java.util.AbstractMap.SimpleImmutableEntry<K, V> oldData = putEntry(key, value, false).getOldData();
            return oldData == null ? null : oldData.getValue();
        }

        boolean putAllEntries(Iterable<? extends Map.Entry<? extends K, ? extends V>> c) {
            if (c == this) {
                return false;
            }
            boolean modified = false;
            for (Map.Entry<? extends K, ? extends V> e : c) {
                V oldValue = put(e.getKey(), e.getValue());
                modified = modified || !Objects.equals(oldValue, e.getValue());
            }
            return modified;
        }

        @SuppressWarnings("unchecked")
        boolean putAllTuples(Iterable<? extends Tuple2<? extends K, ? extends V>> c) {
            if (c instanceof ChampMap<?, ?>) {
                ChampMap<?, ?> that = (ChampMap<?, ?>) c;
                ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
                ChampTrie.BitmapIndexedNode<java.util.AbstractMap.SimpleImmutableEntry<K, V>> newRootNode = root.putAll(makeOwner(), (ChampTrie.Node<java.util.AbstractMap.SimpleImmutableEntry<K, V>>) (ChampTrie.Node<?>) that.root, 0, bulkChange, ChampMap::updateEntry, ChampMap::entryKeyEquals,
                        ChampMap::entryKeyHash, new ChampTrie.ChangeEvent<>());
                if (bulkChange.inBoth == that.size() && !bulkChange.replaced) {
                    return false;
                }
                root = newRootNode;
                size += that.size - bulkChange.inBoth;
                modCount++;
                return true;
            }
            return super.putAllTuples(c);
        }

        ChampTrie.ChangeEvent<java.util.AbstractMap.SimpleImmutableEntry<K, V>> putEntry(final K key, V value, boolean moveToLast) {
            int keyHash = keyHash(key);
            ChampTrie.ChangeEvent<java.util.AbstractMap.SimpleImmutableEntry<K, V>> details = new ChampTrie.ChangeEvent<>();
            root = root.put(makeOwner(), new java.util.AbstractMap.SimpleImmutableEntry<>(key, value), keyHash, 0, details,
                    ChampMap::updateEntry,
                    ChampMap::entryKeyEquals,
                    ChampMap::entryKeyHash);
            if (details.isModified() && !details.isReplaced()) {
                size += 1;
                modCount++;
            }
            return details;
        }

        @SuppressWarnings("unchecked")
        ChampTrie.ChangeEvent<java.util.AbstractMap.SimpleImmutableEntry<K, V>> removeKey(K key) {
            int keyHash = keyHash(key);
            ChampTrie.ChangeEvent<java.util.AbstractMap.SimpleImmutableEntry<K, V>> details = new ChampTrie.ChangeEvent<>();
            root = root.remove(makeOwner(), new java.util.AbstractMap.SimpleImmutableEntry<>(key, null), keyHash, 0, details,
                    ChampMap::entryKeyEquals);
            if (details.isModified()) {
                size = size - 1;
                modCount++;
            }
            return details;
        }

        @SuppressWarnings("unchecked")
        boolean retainAllTuples(Iterable<? extends Tuple2<K, V>> c) {
            if (isEmpty()) {
                return false;
            }
            if (c instanceof Collection<?> && ((Collection<?>) c).isEmpty()
                    || c instanceof Traversable<?> && ((Traversable<?>) c).isEmpty()) {
                clear();
                return true;
            }
            if (c instanceof ChampMap<?, ?>) {
                ChampMap<?, ?> that = (ChampMap<?, ?>) c;
                ChampTrie.BulkChangeEvent bulkChange = new ChampTrie.BulkChangeEvent();
                ChampTrie.BitmapIndexedNode<java.util.AbstractMap.SimpleImmutableEntry<K, V>> newRootNode = root.retainAll(makeOwner(),
                        (ChampTrie.Node<java.util.AbstractMap.SimpleImmutableEntry<K, V>>) (ChampTrie.Node<?>) that.root,
                        0, bulkChange, ChampMap::updateEntry, ChampMap::entryKeyEquals,
                        ChampMap::entryKeyHash, new ChampTrie.ChangeEvent<>());
                if (bulkChange.removed == 0) {
                    return false;
                }
                root = newRootNode;
                size -= bulkChange.removed;
                modCount++;
                return true;
            }
            return super.retainAllTuples(c);
        }

        public ChampMap<K, V> toImmutable() {
            owner = null;
            return isEmpty()
                    ? empty()
                    : new ChampMap<>(root, size);
        }
    }
}
