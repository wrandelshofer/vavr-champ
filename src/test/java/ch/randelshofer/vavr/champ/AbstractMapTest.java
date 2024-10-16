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

import io.vavr.Function1;
import io.vavr.PartialFunction;
import io.vavr.Tuple;
import io.vavr.Tuple2;
import io.vavr.collection.HashMultimap;
import io.vavr.collection.LinkedHashMultimap;
import io.vavr.collection.Seq;
import io.vavr.collection.Stream;
import io.vavr.collection.TreeMultimap;
import io.vavr.control.Option;
import org.assertj.core.api.IterableAssert;
import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.Spliterator;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.BiConsumer;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.regex.Pattern;
import java.util.stream.Collector;

import static ch.randelshofer.vavr.champ.Serializables.deserialize;
import static ch.randelshofer.vavr.champ.Serializables.serialize;
import static io.vavr.API.Some;
import static java.util.Arrays.asList;
import static org.junit.jupiter.api.Assertions.assertThrows;

public abstract class AbstractMapTest extends AbstractTraversableTest {

    protected static Map.Entry<Integer, String> asJavaEntry(int key, String value) {
        return new AbstractMap.SimpleEntry<>(key, value);
    }

    public static String md5(String src) {
        try {
            final MessageDigest md = MessageDigest.getInstance("MD5");
            md.update(src.getBytes(StandardCharsets.UTF_8));
            return toHexString(md.digest());
        } catch (Exception e) {
            throw new IllegalStateException(e);
        }
    }

    /**
     * Returns a string in the hexadecimal format.
     *
     * @param bytes the converted bytes
     * @return the hexadecimal string representing the bytes data
     * @throws IllegalArgumentException if the byte array is null
     */
    public static String toHexString(byte[] bytes) {
        if (bytes == null) {
            throw new IllegalArgumentException("byte array must not be null");
        }

        final StringBuilder hex = new StringBuilder(bytes.length * 2);
        for (byte aByte : bytes) {
            hex.append(Character.forDigit((aByte & 0XF0) >> 4, 16));
            hex.append(Character.forDigit((aByte & 0X0F), 16));
        }
        return hex.toString();
    }

    @SafeVarargs
    protected final <K, V> Map<K, V> asJavaMap(Map.Entry<K, V>... entries) {
        final Map<K, V> results = javaEmptyMap();
        for (Map.Entry<K, V> entry : entries) {
            results.put(entry.getKey(), entry.getValue());
        }
        return results;
    }

    @Override
    protected <T> IterableAssert<T> assertThat(Iterable<T> actual) {
        return new IterableAssert<T>(actual) {
            private Map<T, Integer> countMap(Iterable<? extends T> it) {
                final java.util.HashMap<T, Integer> cnt = new java.util.HashMap<>();
                it.forEach(i -> cnt.merge(i, 1, (v1, v2) -> v1 + v2));
                return cnt;
            }

            @Override
            public IterableAssert<T> isEqualTo(Object obj) {
                @SuppressWarnings("unchecked") final Iterable<T> expected = (Iterable<T>) obj;
                final Map<T, Integer> actualMap = countMap(actual);
                final Map<T, Integer> expectedMap = countMap(expected);
                AbstractMapTest.this.assertThat(actualMap.size()).isEqualTo(expectedMap.size());
                actualMap.forEach((k, v) -> AbstractMapTest.this.assertThat(v).isEqualTo(expectedMap.get(k)));
                return this;
            }
        };
    }

    protected abstract String className();

    @Override
    protected <T> Collector<T, ArrayList<T>, IntMap<T>> collector() {
        final Collector<Tuple2<Integer, T>, ArrayList<Tuple2<Integer, T>>, ? extends io.vavr.collection.Map<Integer, T>> mapCollector = mapCollector();
        return new Collector<T, ArrayList<T>, IntMap<T>>() {
            @Override
            public BiConsumer<ArrayList<T>, T> accumulator() {
                return ArrayList::add;
            }

            @Override
            public Set<Characteristics> characteristics() {
                return mapCollector.characteristics();
            }

            @Override
            public BinaryOperator<ArrayList<T>> combiner() {
                return (left, right) -> fromTuples(mapCollector.combiner().apply(toTuples(left), toTuples(right)));
            }

            @Override
            public Function<ArrayList<T>, IntMap<T>> finisher() {
                return AbstractMapTest.this::ofAll;
            }

            private ArrayList<T> fromTuples(List<Tuple2<Integer, T>> list) {
                final ArrayList<T> result = new ArrayList<>();
                Stream.ofAll(list)
                        .map(tu -> tu._2)
                        .forEach(result::add);
                return result;
            }

            @Override
            public Supplier<ArrayList<T>> supplier() {
                return ArrayList::new;
            }

            private ArrayList<Tuple2<Integer, T>> toTuples(List<T> list) {
                final ArrayList<Tuple2<Integer, T>> result = new ArrayList<>();
                Stream.ofAll(list)
                        .zipWithIndex()
                        .map(tu -> Tuple.of(tu._2, tu._1))
                        .forEach(result::add);
                return result;
            }
        };
    }

    protected abstract <K extends Comparable<? super K>, V, T extends V> Collector<T, ArrayList<T>, ? extends io.vavr.collection.Map<K, V>> collectorWithMapper(
            Function<? super T, ? extends K> keyMapper);

    protected abstract <K extends Comparable<? super K>, V, T> Collector<T, ArrayList<T>, ? extends io.vavr.collection.Map<K, V>> collectorWithMappers(
            Function<? super T, ? extends K> keyMapper, Function<? super T, ? extends V> valueMapper);

    @Override
    protected <T> IntMap<T> empty() {
        return IntMap.of(emptyMap());
    }

    private <T> io.vavr.collection.Map<Integer, T> emptyInt() {
        return emptyMap();
    }

    protected io.vavr.collection.Map<Integer, Integer> emptyIntInt() {
        return emptyMap();
    }

    private io.vavr.collection.Map<Integer, String> emptyIntString() {
        return emptyMap();
    }

    protected abstract <T1 extends Comparable<? super T1>, T2> io.vavr.collection.Map<T1, T2> emptyMap();

    protected boolean emptyMapShouldBeSingleton() {
        return true;
    }

    @Override
    protected boolean emptyShouldBeSingleton() {
        return false;
    }

    @Override
    protected <T> IntMap<T> fill(int n, Supplier<? extends T> s) {
        return tabulate(n, anything -> s.get());
    }

    @Test
    public void forEachByKeyValue() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 2).put(3, 4);
        final int[] result = {0};
        map.forEach((k, v) -> {
            result[0] += k + v;
        });
        assertThat(result[0]).isEqualTo(10);
    }

    @Test
    public void forEachByTuple() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 2).put(3, 4);
        final int[] result = {0};
        map.forEach(t -> {
            result[0] += t._1 + t._2;
        });
        assertThat(result[0]).isEqualTo(10);
    }

    @Override
    protected int getPeekNonNilPerformingAnAction() {
        return 1;
    }

    protected abstract <T1, T2> Map<T1, T2> javaEmptyMap();

    @Test
    public void lift() {
        final Function1<String, Option<Integer>> lifted = mapOf("A", 1).lift();
        assertThat(lifted.apply("A").get()).isEqualTo(1);
        assertThat(lifted.apply("a").isEmpty()).isTrue();
    }

    protected abstract <T> Collector<Tuple2<Integer, T>, ArrayList<Tuple2<Integer, T>>, ? extends io.vavr.collection.Map<Integer, T>> mapCollector();

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapFill(int n, Supplier<? extends Tuple2<? extends K, ? extends V>> s);

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOf(K k1, V v1);

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOf(K k1, V v1, K k2, V v2);

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOf(K k1, V v1, K k2, V v2, K k3, V v3);

    protected abstract <T, K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOf(java.util.stream.Stream<? extends T> stream,
                                                                                                  Function<? super T, ? extends K> keyMapper,
                                                                                                  Function<? super T, ? extends V> valueMapper);

    protected abstract <T, K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOf(java.util.stream.Stream<? extends T> stream,
                                                                                                  Function<? super T, Tuple2<? extends K, ? extends V>> f);

    @SuppressWarnings("unchecked")
    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOfEntries(Map.Entry<? extends K, ? extends V>... entries);

    @SuppressWarnings("unchecked")
    @Test
    public void mapOfEntriesShouldReturnTheSingletonEmpty() {
        if (!emptyMapShouldBeSingleton()) {
            return;
        }
        assertThat(mapOfEntries()).isSameAs(emptyMap());
    }

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOfNullKey(K k1, V v1, K k2, V v2);

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOfNullKey(K k1, V v1, K k2, V v2, K k3, V v3);

    @SuppressWarnings("unchecked")
    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOfTuples(Tuple2<? extends K, ? extends V>... entries);

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapOfTuples(Iterable<? extends Tuple2<? extends K, ? extends V>> entries);

    @SuppressWarnings("unchecked")
    @Test
    public void mapOfTuplesShouldReturnTheSingletonEmpty() {
        if (!emptyMapShouldBeSingleton()) {
            return;
        }
        assertThat(mapOfTuples()).isSameAs(emptyMap());
    }

    protected abstract <K extends Comparable<? super K>, V> io.vavr.collection.Map<K, V> mapTabulate(int n, Function<? super Integer, ? extends Tuple2<? extends K, ? extends V>> f);

    @Override
    protected <T> IntMap<T> of(T element) {
        io.vavr.collection.Map<Integer, T> map = emptyMap();
        map = map.put(0, element);
        return IntMap.of(map);
    }

    @SuppressWarnings("unchecked")
    @Override
    protected <T> IntMap<T> of(T... elements) {
        io.vavr.collection.Map<Integer, T> map = emptyMap();
        for (T element : elements) {
            map = map.put(map.size(), element);
        }
        return IntMap.of(map);
    }

    @Override
    protected <T> IntMap<T> ofAll(Iterable<? extends T> elements) {
        io.vavr.collection.Map<Integer, T> map = emptyMap();
        for (T element : elements) {
            map = map.put(map.size(), element);
        }
        return IntMap.of(map);
    }

    @Override
    protected IntMap<Boolean> ofAll(boolean... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    @Override
    protected IntMap<Byte> ofAll(byte... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    // -- narrow

    @Override
    protected IntMap<Character> ofAll(char... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    // -- mappers collector

    @Override
    protected IntMap<Double> ofAll(double... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    @Override
    protected IntMap<Float> ofAll(float... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    // -- construction

    @Override
    protected IntMap<Integer> ofAll(int... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    @Override
    protected IntMap<Long> ofAll(long... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    @Override
    protected IntMap<Short> ofAll(short... elements) {
        return ofAll(io.vavr.collection.Iterator.ofAll(elements));
    }

    @Override
    protected <T extends Comparable<? super T>> IntMap<T> ofJavaStream(java.util.stream.Stream<? extends T> javaStream) {
        return ofAll(io.vavr.collection.Iterator.ofAll(javaStream.iterator()));
    }

    @Test
    public void putWithTupleWasPresent() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 2)
                .put(Tuple.of(1, 3), (x, y) -> x + y);
        assertThat(map).isEqualTo(emptyIntInt().put(1, 5));
    }

    @Test
    public void putWithTupleWasntPresent() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 2)
                .put(Tuple.of(2, 3), (x, y) -> x + y);
        assertThat(map).isEqualTo(emptyIntInt().put(1, 2).put(2, 3));
    }

    @Test
    public void putWithWasPresent() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 2)
                .put(1, 3, (x, y) -> x + y);
        assertThat(map).isEqualTo(emptyIntInt().put(1, 5));
    }

    @Test
    public void putWithWasntPresent() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 2)
                .put(2, 3, (x, y) -> x + y);
        assertThat(map).isEqualTo(emptyIntInt().put(1, 2).put(2, 3));
    }

    @Test
    public void shouldApplyExistingKey() {
        assertThat(emptyInt().put(1, 2).asPartialFunction().apply(1)).isEqualTo(2);
    }

    @Test
    public void shouldApplyNonExistingKey() {
        assertThrows(NoSuchElementException.class, () -> emptyInt().put(1, 2).asPartialFunction().apply(3));
    }

    @Test
    public void shouldBeTheSame() {
        assertThat(mapOf(1, 2)).isEqualTo(emptyInt().put(1, 2));
    }

    @Test
    public void shouldBiFilterWork() throws Exception {
        final io.vavr.collection.Map<Integer, String> src = mapTabulate(20, n -> Tuple.of(n, Integer.toHexString(n)));
        final Pattern isDigits = Pattern.compile("^\\d+$");
        final io.vavr.collection.Map<Integer, String> dst = src.filter((k, v) -> k % 2 == 0 && isDigits.matcher(v).matches());
        assertThat(dst).isEqualTo(emptyIntString().put(0, "0").put(2, "2").put(4, "4").put(6, "6").put(8, "8").put(16, "10").put(18, "12"));
    }

    @Test
    public void shouldBiMapEmpty() {
        assertThat(emptyInt().bimap(i -> i + 1, o -> o)).isEqualTo(io.vavr.collection.Vector.empty());
    }

    @Test
    public void shouldBiMapNonEmpty() {
        final Seq<Tuple2<Integer, String>> expected = Stream.of(Tuple.of(2, "1!"), Tuple.of(3, "2!"));
        final Seq<Tuple2<Integer, String>> actual = emptyInt().put(1, "1").put(2, "2").bimap(i -> i + 1, s -> s + "!").toStream();
        assertThat(actual).isEqualTo(expected);
    }

    @Override
    @Test
    public void shouldCaclEmptyOrElseSameOther() {
        Iterable<Integer> other = of(42);
        assertThat(empty().orElse(other)).isEqualTo(other);
    }

    @Test
    public void shouldCaclEmptyOrElseSameSupplier() {
        Iterable<Integer> other = of(42);
        Supplier<Iterable<Integer>> supplier = () -> other;
        assertThat(empty().orElse(supplier)).isEqualTo(other);
    }

    @Test
    public void shouldCollectWithKeyMapper() {
        io.vavr.collection.Map<Integer, Integer> map = java.util.stream.Stream.of(1, 2, 3).collect(collectorWithMapper(i -> i * 2));
        assertThat(map).isEqualTo(mapOf(2, 1, 4, 2, 6, 3));
    }

    @Test
    public void shouldCollectWithKeyValueMappers() {
        io.vavr.collection.Map<Integer, String> map = java.util.stream.Stream.of(1, 2, 3).collect(collectorWithMappers(i -> i * 2, String::valueOf));
        assertThat(map).isEqualTo(mapOf(2, "1", 4, "2", 6, "3"));
    }

    @Override
    @Test
    public void shouldComputeDistinctOfNonEmptyTraversable() {
        final io.vavr.collection.Map<Integer, Object> testee = emptyInt().put(1, 1).put(2, 2).put(3, 3);
        assertThat(testee.distinct()).isEqualTo(testee);
    }

    // -- asPartialFunction

    @Test
    public void shouldComputeIfAbsent() {
        final io.vavr.collection.Map<Integer, String> map = emptyIntString().put(1, "v");
        assertThat(map.computeIfAbsent(1, k -> "b")).isEqualTo(Tuple.of("v", map));
        assertThat(map.computeIfAbsent(2, k -> "n")).isEqualTo(Tuple.of("n", emptyIntString().put(1, "v").put(2, "n")));
    }

    @Test
    public void shouldComputeIfPresent() {
        final io.vavr.collection.Map<Integer, String> map = emptyIntString().put(1, "v");
        assertThat(map.computeIfPresent(1, (k, v) -> "b")).isEqualTo(Tuple.of(Option.of("b"), emptyIntString().put(1, "b")));
        assertThat(map.computeIfPresent(2, (k, v) -> "n")).isEqualTo(Tuple.of(Option.none(), map));
    }

    @Test
    public void shouldConstructFromEntriesIterable() {
        final io.vavr.collection.Map<String, Integer> actual = mapOfTuples(asList(io.vavr.collection.Map.entry("1", 1), io.vavr.collection.Map.entry("2", 2), io.vavr.collection.Map.entry("3", 3)));
        final io.vavr.collection.Map<String, Integer> expected = this.<String, Integer>emptyMap().put("1", 1).put("2", 2).put("3", 3);
        assertThat(actual).isEqualTo(expected);
    }

    // -- equality

    @Test
    public void shouldConstructFromEntriesIterableWithDuplicatedKeys() {
        assertThat(mapOfTuples(asList(
                io.vavr.collection.Map.entry(1, "1"), io.vavr.collection.Map.entry(1, "2"),
                io.vavr.collection.Map.entry(2, "3"), io.vavr.collection.Map.entry(2, "4")
        )))
                .hasSize(2)
                .isEqualTo(mapOf(1, "2", 2, "4"));
    }

    // -- head

    @Test
    @SuppressWarnings("unchecked")
    public void shouldConstructFromEntriesVararg() {
        final io.vavr.collection.Map<String, Integer> actual = mapOfTuples(io.vavr.collection.Map.entry("1", 1), io.vavr.collection.Map.entry("2", 2), io.vavr.collection.Map.entry("3", 3));
        final io.vavr.collection.Map<String, Integer> expected = this.<String, Integer>emptyMap().put("1", 1).put("2", 2).put("3", 3);
        assertThat(actual).isEqualTo(expected);
    }

    // -- init

    @Test
    @SuppressWarnings("unchecked")
    public void shouldConstructFromEntriesVarargWithDuplicatedKeys() {
        assertThat(mapOfTuples(
                io.vavr.collection.Map.entry(1, "1"), io.vavr.collection.Map.entry(1, "2"),
                io.vavr.collection.Map.entry(2, "3"), io.vavr.collection.Map.entry(2, "4")
        ))
                .hasSize(2)
                .isEqualTo(mapOf(1, "2", 2, "4"));
    }

    // -- tail

    @Test
    public void shouldConstructFromJavaStream() {
        final java.util.stream.Stream<Integer> javaStream = java.util.stream.Stream.of(1, 2, 3);
        final io.vavr.collection.Map<String, Integer> map = mapOf(javaStream, String::valueOf, Function.identity());
        assertThat(map).isEqualTo(this.<String, Integer>emptyMap().put("1", 1).put("2", 2).put("3", 3));
    }

    // -- toString

    @Test
    public void shouldConstructFromJavaStreamEntries() {
        final java.util.stream.Stream<Integer> javaStream = java.util.stream.Stream.of(1, 2, 3);
        final io.vavr.collection.Map<String, Integer> map = mapOf(javaStream, i -> Tuple.of(String.valueOf(i), i));
        assertThat(map).isEqualTo(this.<String, Integer>emptyMap().put("1", 1).put("2", 2).put("3", 3));
    }

    // -- toJavaMap

    @Test
    public void shouldConstructFromJavaStreamEntriesWithDuplicatedKeys() {
        assertThat(mapOf(Stream.range(0, 4).toJavaStream(), i ->
                io.vavr.collection.Map.entry(Math.max(1, Math.min(i, 2)), String.valueOf(i + 1))
        ))
                .hasSize(2)
                .isEqualTo(mapOf(1, "2", 2, "4"));
    }

    // -- contains

    @Test
    public void shouldConstructFromJavaStreamWithDuplicatedKeys() {
        assertThat(mapOf(Stream.range(0, 4).toJavaStream()
                , i -> Math.max(1, Math.min(i, 2))
                , i -> String.valueOf(i + 1)
        ))
                .hasSize(2)
                .isEqualTo(mapOf(1, "2", 2, "4"));
    }

    @Test
    public void shouldConstructFromPairs() {
        final io.vavr.collection.Map<String, Integer> actual = mapOf("1", 1, "2", 2, "3", 3);
        final io.vavr.collection.Map<String, Integer> expected = this.<String, Integer>emptyMap().put("1", 1).put("2", 2).put("3", 3);
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldConstructFromPairsWithDuplicatedKeys() {
        final io.vavr.collection.Map<Integer, String> actual = mapOf(1, "1", 1, "2", 2, "3");
        final io.vavr.collection.Map<Integer, String> expected = this.<Integer, String>emptyMap().put(1, "2").put(2, "3");
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    @SuppressWarnings("unchecked")
    public void shouldConstructFromUtilEntries() {
        final io.vavr.collection.Map<Integer, String> actual = mapOfEntries(asJavaEntry(1, "1"), asJavaEntry(2, "2"), asJavaEntry(3, "3"));
        final io.vavr.collection.Map<Integer, String> expected = this.<Integer, String>emptyMap().put(1, "1").put(2, "2").put(3, "3");
        assertThat(actual).isEqualTo(expected);
    }

    // -- flatMap

    @Test
    @SuppressWarnings("unchecked")
    public void shouldConstructFromUtilEntriesWithDuplicatedKeys() {
        assertThat(mapOfEntries(
                asJavaEntry(1, "1"), asJavaEntry(1, "2"),
                asJavaEntry(2, "3"), asJavaEntry(2, "4")
        ))
                .hasSize(2)
                .isEqualTo(mapOf(1, "2", 2, "4"));
    }

    // -- keySet

    @Test
    public void shouldConstructWithFill() {
        AtomicInteger i = new AtomicInteger();
        final io.vavr.collection.Map<String, Integer> actual = mapFill(4, () -> Tuple.of(String.valueOf(i.get()), i.getAndIncrement()));
        final io.vavr.collection.Map<String, Integer> expected = this.<String, Integer>emptyMap().put("0", 0).put("1", 1).put("2", 2).put("3", 3);
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldConstructWithFillWithDuplicatedKeys() {
        AtomicInteger i = new AtomicInteger();
        assertThat(mapFill(4, () ->
                Tuple.of(Math.max(1, Math.min(i.get(), 2)), String.valueOf(i.getAndIncrement() + 1))
        ))
                .hasSize(2)
                .isEqualTo(mapOf(1, "2", 2, "4"));
    }

    // -- values

    @Test
    public void shouldConstructWithTabulate() {
        final io.vavr.collection.Map<String, Integer> actual = mapTabulate(4, i -> Tuple.of(i.toString(), i));
        final io.vavr.collection.Map<String, Integer> expected = this.<String, Integer>emptyMap().put("0", 0).put("1", 1).put("2", 2).put("3", 3);
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldConstructWithTabulateWithDuplicatedKeys() {
        assertThat(mapTabulate(4, i ->
                Tuple.of(Math.max(1, Math.min(i, 2)), String.valueOf(i + 1))
        ))
                .hasSize(2)
                .isEqualTo(mapOf(1, "2", 2, "4"));
    }

    // -- biMap

    @Test
    public void shouldConvertToJavaMap() {
        final io.vavr.collection.Map<Integer, String> actual = mapOf(1, "1", 2, "2", 3, "3");
        final Map<Integer, String> expected = asJavaMap(asJavaEntry(1, "1"), asJavaEntry(2, "2"), asJavaEntry(3, "3"));
        assertThat(actual.toJavaMap()).isEqualTo(expected);
    }

    @SuppressWarnings("unchecked")
    @Test
    public void shouldFillTheSeqCallingTheSupplierInTheRightOrder() {
        final LinkedList<Integer> ints = new LinkedList<>(asList(0, 0, 1, 1, 2, 2));
        final Supplier<Tuple2<Long, Float>> s = () -> new Tuple2<>(ints.remove().longValue(), ints.remove().floatValue());
        final io.vavr.collection.Map<Long, Float> actual = mapFill(3, s);
        assertThat(actual).isEqualTo(mapOfTuples(new Tuple2<>(0l, 0f), new Tuple2<>(1l, 1f), new Tuple2<>(2l, 2f)));
    }

    // -- orElse
    // DEV-Note: IntMap converts `other` to map

    @Test
    public void shouldFillTheSeqWith0Elements() {
        assertThat(mapFill(0, () -> new Tuple2<>(1, 1))).isEqualTo(empty());
    }

    @Test
    public void shouldFillTheSeqWith0ElementsWhenNIsNegative() {
        assertThat(mapFill(-1, () -> new Tuple2<>(1, 1))).isEqualTo(empty());
    }

    // -- map

    @Test
    public void shouldFindKey() {
        assertThat(emptyInt().put(1, 2).containsKey(1)).isTrue();
        assertThat(emptyInt().put(1, 2).containsKey(2)).isFalse();
    }

    @Test
    public void shouldFindValue() {
        assertThat(emptyInt().put(1, 2).containsValue(2)).isTrue();
        assertThat(emptyInt().put(1, 2).containsValue(1)).isFalse();
    }

    @SuppressWarnings("unchecked")
    @Test
    public void shouldFlatMapUsingBiFunction() {
        final io.vavr.collection.Map<Integer, Integer> testee = mapOfTuples(Tuple.of(1, 11), Tuple.of(2, 22), Tuple.of(3, 33));
        final io.vavr.collection.Map<String, String> actual = testee
                .flatMap((k, v) -> io.vavr.collection.List.of(Tuple.of(String.valueOf(k), String.valueOf(v)),
                        Tuple.of(String.valueOf(k * 10), String.valueOf(v * 10))));
        final io.vavr.collection.Map<String, String> expected = mapOfTuples(Tuple.of("1", "11"), Tuple.of("10", "110"), Tuple.of("2", "22"),
                Tuple.of("20", "220"), Tuple.of("3", "33"), Tuple.of("30", "330"));
        assertThat(actual).isEqualTo(expected);
    }

    @Override
    @Test
    public void shouldFoldRightNonNil() {
        final String actual = of('a', 'b', 'c').foldRight("", (x, xs) -> x + xs);
        final io.vavr.collection.List<String> expected = io.vavr.collection.List.of('a', 'b', 'c').permutations().map(io.vavr.collection.List::mkString);
        assertThat(actual).isIn(expected);
    }

    @Test
    public void shouldGetAPresentNullValueWhenPutFirstHavingTwoEntries() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, null, 2, "b");
        assertThat(map.get(1)).isEqualTo(Some(null));
    }

    @Test
    public void shouldGetAPresentNullValueWhenPutLastHavingTwoEntries() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, null);
        assertThat(map.get(2)).isEqualTo(Some(null));
    }

    @Test
    public void shouldGetValueOfNullKeyWhenPutFirstHavingTwoEntries() {
        final io.vavr.collection.Map<Integer, String> map = mapOfNullKey(null, "a", 2, "b");
        assertThat(map.get(null)).isEqualTo(Some("a"));
    }

    @Test
    public void shouldGetValueOfNullKeyWhenPutLastHavingTwoEntries() {
        final io.vavr.collection.Map<Integer, String> map = mapOfNullKey(1, "a", null, "b");
        assertThat(map.get(null)).isEqualTo(Some("b"));
    }

    @Test
    public void shouldHaveDistinctSpliterator() {
        assertThat(of(1, 2, 3).spliterator().hasCharacteristics(Spliterator.DISTINCT)).isTrue();
    }

    @Test
    public void shouldHaveSizedSpliterator() {
        assertThat(of(1, 2, 3).spliterator().hasCharacteristics(Spliterator.SIZED | Spliterator.SUBSIZED)).isTrue();
    }

    @Test
    public void shouldIgnoreOrderOfEntriesWhenComparingForEquality() {
        final io.vavr.collection.Map<?, ?> map1 = emptyInt().put(1, 'a').put(2, 'b').put(3, 'c');
        final io.vavr.collection.Map<?, ?> map2 = emptyInt().put(3, 'c').put(2, 'b').put(1, 'a').remove(2).put(2, 'b');
        assertThat(map1).isEqualTo(map2);
    }

    // -- merge(Map)

    @Test
    public void shouldImplementPartialFunction() {
        PartialFunction<Integer, String> f = mapOf(1, "1").asPartialFunction();
        assertThat(f.isDefinedAt(1)).isTrue();
        assertThat(f.apply(1)).isEqualTo("1");
        assertThat(f.isDefinedAt(2)).isFalse();
    }

    @Test
    public void shouldKeyFilterWork() throws Exception {
        final io.vavr.collection.Map<Integer, String> src = mapTabulate(20, n -> Tuple.of(n, Integer.toHexString(n)));
        final io.vavr.collection.Map<Integer, String> dst = src.filterKeys(k -> k % 2 == 0);
        assertThat(dst).isEqualTo(emptyIntString().put(0, "0").put(2, "2").put(4, "4").put(6, "6").put(8, "8").put(10, "a").put(12, "c").put(14, "e").put(16, "10").put(18, "12"));
    }

    @Test
    public void shouldMakeString() {
        assertThat(emptyMap().toString()).isEqualTo(className() + "()");
        assertThat(emptyInt().put(1, 2).toString()).isEqualTo(className() + "(" + Tuple.of(1, 2) + ")");
    }

    // -- merge(Map, BiFunction)

    @Test
    public void shouldMapEmpty() {
        assertThat(emptyInt().map(Tuple2::_1)).isEqualTo(io.vavr.collection.Vector.empty());
    }

    @Test
    public void shouldMapNonEmpty() {
        final Seq<Integer> expected = io.vavr.collection.Vector.of(1, 2);
        final Seq<Integer> actual = emptyInt().put(1, "1").put(2, "2").map(Tuple2::_1);
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldMerge() {
        final io.vavr.collection.Map<Integer, Integer> m1 = emptyIntInt().put(1, 1).put(2, 2);
        final io.vavr.collection.Map<Integer, Integer> m2 = emptyIntInt().put(1, 1).put(4, 4);
        final io.vavr.collection.Map<Integer, Integer> m3 = emptyIntInt().put(3, 3).put(4, 4);
        assertThat(m1.merge(m2)).isEqualTo(emptyIntInt().put(1, 1).put(2, 2).put(4, 4));
        assertThat(m1.merge(m3)).isEqualTo(emptyIntInt().put(1, 1).put(2, 2).put(3, 3).put(4, 4));
    }

    // -- equality

    @Test
    public void shouldMergeCollisions() {
        final io.vavr.collection.Map<Integer, Integer> m1 = emptyIntInt().put(1, 1).put(2, 2);
        final io.vavr.collection.Map<Integer, Integer> m2 = emptyIntInt().put(1, 2).put(4, 4);
        final io.vavr.collection.Map<Integer, Integer> m3 = emptyIntInt().put(3, 3).put(4, 4);
        assertThat(emptyIntInt().merge(m2, Math::max)).isEqualTo(m2);
        assertThat(m2.merge(emptyIntInt(), Math::max)).isEqualTo(m2);
        assertThat(m1.merge(m2, Math::max)).isEqualTo(emptyIntInt().put(1, 2).put(2, 2).put(4, 4));
        assertThat(m1.merge(m3, Math::max)).isEqualTo(emptyIntInt().put(1, 1).put(2, 2).put(3, 3).put(4, 4));
    }

    // -- put

    @Test
    public void shouldNarrowMap() {
        final io.vavr.collection.Map<Integer, Double> int2doubleMap = mapOf(1, 1.0d);
        final io.vavr.collection.Map<Number, Number> number2numberMap = io.vavr.collection.Map.narrow(int2doubleMap);
        final int actual = number2numberMap.put(new BigDecimal("2"), new BigDecimal("2.0")).values().sum().intValue();
        assertThat(actual).isEqualTo(3);
    }

    @Override
    @Test
    public void shouldNonNilGroupByIdentity() {
        final io.vavr.collection.Map<?, ?> actual = of('a', 'b', 'c').groupBy(Function.identity());
        final io.vavr.collection.Map<?, ?> expected = io.vavr.collection.LinkedHashMap.empty().put('a', mapOf(0, 'a')).put('b', mapOf(1, 'b'))
                .put('c', mapOf(2, 'c'));
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldObeyEqualityConstraints() {

        // sequential collections
        assertThat(emptyMap().equals(io.vavr.collection.HashMap.empty())).isTrue();
        assertThat(mapOf(1, "a").equals(io.vavr.collection.HashMap.of(1, "a"))).isTrue();
        assertThat(mapOf(1, "a", 2, "b", 3, "c").equals(io.vavr.collection.HashMap.of(1, "a", 2, "b", 3, "c"))).isTrue();
        assertThat(mapOf(1, "a", 2, "b", 3, "c").equals(io.vavr.collection.HashMap.of(3, "c", 2, "b", 1, "a"))).isTrue();

        // other classes
        assertThat(empty().equals(io.vavr.collection.List.empty())).isFalse();
        assertThat(empty().equals(HashMultimap.withSeq().empty())).isFalse();
        assertThat(empty().equals(io.vavr.collection.HashSet.empty())).isFalse();

        assertThat(empty().equals(LinkedHashMultimap.withSeq().empty())).isFalse();
        assertThat(empty().equals(io.vavr.collection.LinkedHashSet.empty())).isFalse();

        assertThat(empty().equals(TreeMultimap.withSeq().empty())).isFalse();
        assertThat(empty().equals(io.vavr.collection.TreeSet.empty())).isFalse();
    }

    @Test
    public void shouldPartitionInOneIteration() {
        final AtomicInteger count = new AtomicInteger(0);
        final io.vavr.collection.Map<String, Integer> map = mapOf("1", 1, "2", 2, "3", 3);
        final Tuple2<? extends io.vavr.collection.Map<String, Integer>, ? extends io.vavr.collection.Map<String, Integer>> results = map.partition(entry -> {
            count.incrementAndGet();
            return true;
        });
        assertThat(results._1).isEqualTo(mapOf("1", 1, "2", 2, "3", 3));
        assertThat(results._2).isEmpty();
        assertThat(count.get()).isEqualTo(3);
    }

    // -- remove

    @Override
    @Test
    @SuppressWarnings("unchecked")
    public void shouldPartitionIntsInOddAndEvenHavingOddAndEvenNumbers() {
        assertThat(of(1, 2, 3, 4).partition(i -> i % 2 != 0))
                .isEqualTo(Tuple.of(mapOfTuples(Tuple.of(0, 1), Tuple.of(2, 3)),
                        mapOfTuples(Tuple.of(1, 2), Tuple.of(3, 4))));
    }

    @Override
    @Test
    public void shouldPreserveSingletonInstanceOnDeserialization() {
        final io.vavr.collection.Map<?, ?> obj = deserialize(serialize(emptyMap()));
        final boolean actual = obj == emptyMap();
        assertThat(actual).isTrue();
    }

    // -- removeAll

    @Test
    public void shouldPutExistingKeyAndEqualValue() {
        final io.vavr.collection.Map<IntMod2, String> map = mapOf(new IntMod2(1), "a");

        // we need to compare Strings because equals (intentionally) does not work for IntMod2
        final String actual = map.put(new IntMod2(3), "a").toString();
        final String expected = map.stringPrefix() + "((3, a))";

        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldPutExistingKeyAndNonEqualValue() {
        final io.vavr.collection.Map<IntMod2, String> map = mapOf(new IntMod2(1), "a");

        // we need to compare Strings because equals (intentionally) does not work for IntMod2
        final String actual = map.put(new IntMod2(3), "b").toString();
        final String expected = map.stringPrefix() + "((3, b))";

        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldPutNullKeyIntoMapThatContainsNullKey() {
        final io.vavr.collection.Map<Integer, String> map = mapOfNullKey(1, "a", null, "b", 2, "c");
        assertThat(map.put(null, "!")).isEqualTo(mapOfNullKey(1, "a", null, "!", 2, "c"));
    }

    // -- transform

    @Test
    public void shouldPutTuple() {
        assertThat(emptyIntInt().put(Tuple.of(1, 2))).isEqualTo(emptyIntInt().put(1, 2));
    }

    // -- zip

    @Test
    public void shouldRecognizeContainedKeyValuePair() {
        final io.vavr.collection.TreeMap<String, Integer> testee = io.vavr.collection.TreeMap.of(Tuple.of("one", 1));
        assertThat(testee.contains(Tuple.of("one", 1))).isTrue();
    }

    @Test
    public void shouldRecognizeNotContainedKeyValuePair() {
        final io.vavr.collection.TreeMap<String, Integer> testee = io.vavr.collection.TreeMap.of(Tuple.of("one", 1));
        assertThat(testee.contains(Tuple.of("one", 0))).isFalse();
    }

    @Test
    public void shouldRemoveAllKeys() {
        final io.vavr.collection.Map<Integer, Object> src = emptyInt().put(1, 'a').put(2, 'b').put(3, 'c');
        assertThat(src.removeAll(io.vavr.collection.List.of(1, 3))).isEqualTo(emptyInt().put(2, 'b'));
        assertThat(src.removeAll(io.vavr.collection.List.of(33))).isSameAs(src);
        assertThat(src.removeAll(io.vavr.collection.List.empty())).isSameAs(src);
    }

    @Test
    public void shouldRemoveFromMapThatContainsFirstEntryHavingNullKey() {
        final io.vavr.collection.Map<Integer, String> map = mapOfNullKey(null, "a", 1, "b", 2, "c");
        assertThat(map.remove(1)).isEqualTo(mapOfNullKey(null, "a", 2, "c"));
    }

    @Test
    public void shouldRemoveKey() {
        final io.vavr.collection.Map<Integer, Object> src = emptyInt().put(1, 'a').put(2, 'b').put(3, 'c');
        assertThat(src.remove(2)).isEqualTo(emptyInt().put(1, 'a').put(3, 'c'));
        assertThat(src.remove(33)).isSameAs(src);
    }

    @Test
    public void shouldReplaceAllValuesWithFunctionResult() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b");
        final io.vavr.collection.Map<Integer, String> actual = map.replaceAll((integer, s) -> s + integer);
        final io.vavr.collection.Map<Integer, String> expected = mapOf(1, "a1", 2, "b2");
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldReplaceCurrentValueForExistingKey() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b");
        final io.vavr.collection.Map<Integer, String> actual = map.replaceValue(2, "c");
        final io.vavr.collection.Map<Integer, String> expected = mapOf(1, "a", 2, "c");
        assertThat(actual).isEqualTo(expected);
    }

    // -- zipWithIndex

    @Test
    public void shouldReplaceCurrentValueForExistingKeyAndEqualOldValue() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b");
        final io.vavr.collection.Map<Integer, String> actual = map.replace(2, "b", "c");
        final io.vavr.collection.Map<Integer, String> expected = mapOf(1, "a", 2, "c");
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldReturnDefaultValue() {
        final io.vavr.collection.Map<String, String> map = mapOf("1", "a").put("2", "b");
        assertThat(map.getOrElse("3", "3")).isEqualTo("3");
    }

    // -- zipAll

    @Test
    public void shouldReturnEmptySetWhenAskedForTuple2SetOfAnEmptyMap() {
        assertThat(emptyMap().toSet()).isEqualTo(io.vavr.collection.HashSet.empty());
    }

    @Test
    @SuppressWarnings("unchecked")
    public void shouldReturnKeySet() {
        final io.vavr.collection.Set<Integer> actual = mapOfTuples(Tuple.of(1, 11), Tuple.of(2, 22), Tuple.of(3, 33)).keySet();
        assertThat(actual).isEqualTo(io.vavr.collection.HashSet.of(1, 2, 3));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void shouldReturnKeysIterator() {
        final io.vavr.collection.Iterator<Integer> actual = mapOfTuples(Tuple.of(1, 11), Tuple.of(2, 22), Tuple.of(3, 33)).keysIterator();
        assertThat(actual).isEqualTo(io.vavr.collection.Iterator.of(1, 2, 3));
    }

    @Test
    public void shouldReturnListWithMappedValues() {
        assertThat(emptyIntInt().put(1, 1).put(2, 2).iterator((a, b) -> a + b).toList()).isEqualTo(io.vavr.collection.List.of(2, 4));
    }

    @Test
    public void shouldReturnModifiedKeysMap() {
        final io.vavr.collection.Map<String, String> actual = emptyIntString().put(1, "1").put(2, "2").mapKeys(k -> k * 12).mapKeys(Integer::toHexString).mapKeys(String::toUpperCase);
        final io.vavr.collection.Map<String, String> expected = this.<String, String>emptyMap().put("C", "1").put("18", "2");
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldReturnModifiedKeysMapWithNonUniqueMapper() {
        final io.vavr.collection.Map<Integer, String> actual = emptyIntString()
                .put(1, "1").put(2, "2").put(3, "3")
                .mapKeys(k -> k * 118).mapKeys(Integer::toHexString).mapKeys(AbstractMapTest::md5).mapKeys(String::length);
        assertThat(actual).hasSize(1);
        assertThat(actual.values()).hasSize(1);
        //In different cases (based on items order) transformed map may contain different values
        assertThat(actual.values().head()).isIn("1", "2", "3");
    }

    @Test
    public void shouldReturnModifiedKeysMapWithNonUniqueMapperAndMergedValues() {
        final io.vavr.collection.Map<Integer, String> actual = emptyIntString()
                .put(1, "1").put(2, "2").put(3, "3")
                .mapKeys(k -> k * 118).mapKeys(Integer::toHexString).mapKeys(AbstractMapTest::md5)//Unique key mappers
                .mapKeys(String::length, (v1, v2) -> io.vavr.collection.List.of(v1.split("#")).append(v2).sorted().mkString("#"));
        final io.vavr.collection.Map<Integer, String> expected = emptyIntString().put(32, "1#2#3");
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldReturnModifiedValuesMap() {
        assertThat(emptyIntString().put(1, "1").put(2, "2").mapValues(Integer::parseInt)).isEqualTo(emptyInt().put(1, 1).put(2, 2));
    }

    @Test
    public void shouldReturnNoneWhenAccessingAbsentKeysInAMapWithNulls() {
        final io.vavr.collection.Map<String, String> map = mapOf("1", "a").put("2", null);
        assertThat(map.get("3")).isEqualTo(Option.none());
    }

    // -- special cases

    @Test
    public void shouldReturnOptionOfKeyWhenAccessingPresentKeysInAMapWithNulls() {
        final io.vavr.collection.Map<String, String> map = mapOf("1", "a").put("2", null);
        assertThat(map.get("1")).isEqualTo(Option.of("a"));
    }

    @Test
    public void shouldReturnOptionOfNullWhenAccessingKeysSetToNull() {
        final io.vavr.collection.Map<String, String> map = mapOf("1", null);
        assertThat(map.get("1")).isEqualTo(Option.some(null));
    }

    @Test
    public void shouldReturnSameInstanceForExistingKeyAndNonEqualOldValue() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b");
        final io.vavr.collection.Map<Integer, String> actual = map.replace(2, "d", "c");
        assertThat(actual).isSameAs(map);
    }

    @Test
    public void shouldReturnSameInstanceIfReplacingCurrentValueWithNonExistingKey() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b");
        final io.vavr.collection.Map<Integer, String> actual = map.replaceValue(3, "?");
        assertThat(actual).isSameAs(map);
    }

    @Test
    public void shouldReturnSameInstanceIfReplacingCurrentValueWithOldValueWithNonExistingKey() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b");
        final io.vavr.collection.Map<Integer, String> actual = map.replace(3, "?", "!");
        assertThat(actual).isSameAs(map);
    }

    // -- forEach

    @Test
    public void shouldReturnSameMapWhenEmptyRemoveAllNonEmpty() {
        final io.vavr.collection.Map<Integer, String> empty = emptyMap();
        assertThat(empty.removeAll(io.vavr.collection.List.of(1, 2, 3))).isSameAs(empty);
    }

    @Test
    public void shouldReturnSameMapWhenMergeEmptyWithNonEmpty() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b", 3, "c");
        if (map.isOrdered()) {
            assertThat(this.<Integer, String>emptyMap().merge(map)).isEqualTo(map);
        } else {
            assertThat(this.<Integer, String>emptyMap().merge(map)).isSameAs(map);
        }
    }

    // -- put with merge function

    @Test
    public void shouldReturnSameMapWhenMergeEmptyWithNonEmptyUsingCollisionResolution() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 1, 2, 2, 3, 3);
        if (map.isOrdered()) {
            assertThat(this.<Integer, Integer>emptyMap().merge(map, Math::max)).isEqualTo(map);
        } else {
            assertThat(this.<Integer, Integer>emptyMap().merge(map, Math::max)).isSameAs(map);
        }
    }

    @Test
    public void shouldReturnSameMapWhenMergeNonEmptyWithEmpty() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b", 3, "c");
        assertThat(map.merge(emptyMap())).isSameAs(map);
    }

    @Test
    public void shouldReturnSameMapWhenMergeNonEmptyWithEmptyUsingCollisionResolution() {
        final io.vavr.collection.Map<Integer, Integer> map = mapOf(1, 1, 2, 2, 3, 3);
        assertThat(map.merge(emptyMap(), Math::max)).isSameAs(map);
    }

    @Test
    public void shouldReturnSameMapWhenNonEmptyRemoveAllEmpty() {
        final io.vavr.collection.Map<Integer, String> map = mapOf(1, "a", 2, "b", 3, "c");
        assertThat(map.removeAll(io.vavr.collection.List.empty())).isSameAs(map);
    }

    @Test
    public void shouldReturnSingleMapAfterFillWithConstantKeys() {
        AtomicInteger value = new AtomicInteger(83);
        assertThat(mapFill(17, () -> Tuple.of(7, value.getAndIncrement())))
                .hasSize(1)
                .isEqualTo(mapOf(7, value.decrementAndGet()));
    }

    @Test
    public void shouldReturnSizeWhenSpliterator() {
        assertThat(of(1, 2, 3).spliterator().getExactSizeIfKnown()).isEqualTo(3);
    }

    @Override
    @Test
    public void shouldReturnSomeTailWhenCallingTailOptionOnNonNil() {
        assertThat(of(1, 2, 3).tailOption().get()).isEqualTo(Option.some(of(2, 3)).get());
    }

    @Test
    public void shouldReturnTuple2SetOfANonEmptyMap() {
        assertThat(emptyInt().put(1, "1").put(2, "2").toSet()).isEqualTo(io.vavr.collection.HashSet.of(Tuple.of(1, "1"), Tuple.of(2, "2")));
    }

    // -- fill(int, Supplier)

    @Test
    @SuppressWarnings("unchecked")
    public void shouldReturnValuesIterator() {
        final io.vavr.collection.Iterator<Integer> actual = mapOfTuples(Tuple.of(1, 11), Tuple.of(2, 22), Tuple.of(3, 33)).valuesIterator();
        assertThat(actual).isEqualTo(io.vavr.collection.Iterator.of(11, 22, 33));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void shouldReturnValuesSeq() {
        final Seq<Integer> actual = mapOfTuples(Tuple.of(1, 11), Tuple.of(2, 22), Tuple.of(3, 33)).values();
        assertThat(actual).isEqualTo(io.vavr.collection.Iterator.of(11, 22, 33));
    }

    @Test
    public void shouldSerializeDeserializeNonEmptyMap() {
        final Object expected = of('a', 'b', 'c');
        final Object actual = deserialize(serialize(expected));
        assertThat(actual).isEqualTo(expected);
    }

    @Override
    @Test
    @SuppressWarnings("unchecked")
    public void shouldSpanAndNotTruncate() {
        assertThat(of(1, 1, 2, 2, 3, 3).span(x -> x % 2 == 1))
                .isEqualTo(Tuple.of(mapOfTuples(Tuple.of(0, 1), Tuple.of(1, 1)),
                        mapOfTuples(Tuple.of(2, 2), Tuple.of(3, 2),
                                Tuple.of(4, 3), Tuple.of(5, 3))));
        assertThat(of(1, 1, 2, 2, 4, 4).span(x -> x == 1))
                .isEqualTo(Tuple.of(mapOfTuples(Tuple.of(0, 1), Tuple.of(1, 1)),
                        mapOfTuples(Tuple.of(2, 2), Tuple.of(3, 2),
                                Tuple.of(4, 4), Tuple.of(5, 4))));
    }

    @Override
    @Test
    @SuppressWarnings("unchecked")
    public void shouldSpanNonNil() {
        assertThat(of(0, 1, 2, 3).span(i -> i < 2))
                .isEqualTo(Tuple.of(mapOfTuples(Tuple.of(0, 0), Tuple.of(1, 1)),
                        mapOfTuples(Tuple.of(2, 2), Tuple.of(3, 3))));
    }

    @SuppressWarnings("unchecked")
    @Test
    public void shouldTabulateTheSeq() {
        final Function<Number, Tuple2<Long, Float>> f = i -> new Tuple2<>(i.longValue(), i.floatValue());
        final io.vavr.collection.Map<Long, Float> map = mapTabulate(3, f);
        assertThat(map).isEqualTo(mapOfTuples(new Tuple2<>(0l, 0f), new Tuple2<>(1l, 1f), new Tuple2<>(2l, 2f)));
    }

    @SuppressWarnings("unchecked")
    @Test
    public void shouldTabulateTheSeqCallingTheFunctionInTheRightOrder() {
        final LinkedList<Integer> ints = new LinkedList<>(asList(0, 0, 1, 1, 2, 2));
        final Function<Integer, Tuple2<Long, Float>> f = i -> new Tuple2<>(ints.remove().longValue(), ints.remove().floatValue());
        final io.vavr.collection.Map<Long, Float> map = mapTabulate(3, f);
        assertThat(map).isEqualTo(mapOfTuples(new Tuple2<>(0l, 0f), new Tuple2<>(1l, 1f), new Tuple2<>(2l, 2f)));
    }

    // -- filter

    @Test
    public void shouldTabulateTheSeqWith0Elements() {
        assertThat(mapTabulate(0, i -> new Tuple2<>(i, i))).isEqualTo(empty());
    }

    @Test
    public void shouldTabulateTheSeqWith0ElementsWhenNIsNegative() {
        assertThat(mapTabulate(-1, i -> new Tuple2<>(i, i))).isEqualTo(empty());
    }

    @Test
    public void shouldThrowIfZipAllWithThatIsNull() {
        assertThrows(NullPointerException.class, () -> emptyMap().zipAll(null, null, null));
    }


    // -- computeIfAbsent

    @Test
    public void shouldThrowIfZipWithThatIsNull() {
        assertThrows(NullPointerException.class, () -> emptyMap().zip(null));
    }

    // -- computeIfAbsent

    @Test
    public void shouldThrowWhenHeadEmpty() {
        assertThrows(NoSuchElementException.class, () -> emptyMap().head());
    }

    // -- get with nulls

    @Test
    public void shouldThrowWhenInitEmpty() {
        assertThrows(UnsupportedOperationException.class, () -> emptyMap().init());
    }

    @Test
    public void shouldThrowWhenTailEmpty() {
        assertThrows(UnsupportedOperationException.class, () -> emptyMap().tail());
    }

    @Test
    public void shouldTransform() {
        final io.vavr.collection.Map<?, ?> actual = emptyIntInt().put(1, 11).transform(map -> map.put(2, 22));
        assertThat(actual).isEqualTo(emptyIntInt().put(1, 11).put(2, 22));
    }

    @Test
    public void shouldValueFilterWork() throws Exception {
        final io.vavr.collection.Map<Integer, String> src = mapTabulate(10, n -> Tuple.of(n, Integer.toHexString(n)));
        final Pattern isDigits = Pattern.compile("^\\d+$");
        final io.vavr.collection.Map<Integer, String> dst = src.filterValues(v -> isDigits.matcher(v).matches());
        assertThat(dst).isEqualTo(emptyIntString().put(0, "0").put(1, "1").put(2, "2").put(3, "3").put(4, "4").put(5, "5").put(6, "6").put(7, "7").put(8, "8").put(9, "9"));
    }

    @Test
    public void shouldZipAllEmptyAndNonNil() {
        final Seq<Tuple2<Tuple2<Integer, Object>, Object>> actual = emptyInt().zipAll(io.vavr.collection.List.of(1), null, null);
        assertThat(actual).isEqualTo(Stream.of(Tuple.of(null, 1)));
    }

    @Test
    public void shouldZipAllNils() {
        final Seq<Tuple2<Tuple2<Integer, Object>, Object>> actual = emptyInt().zipAll(empty(), null, null);
        assertThat(actual).isEqualTo(Stream.empty());
    }

    @Test
    public void shouldZipAllNonEmptyAndNil() {
        final Seq<Tuple2<Tuple2<Integer, Object>, Object>> actual = emptyInt().put(0, 1).zipAll(empty(), null, null);
        assertThat(actual).isEqualTo(Stream.of(Tuple.of(Tuple.of(0, 1), null)));
    }

    @Test
    public void shouldZipAllNonNilsIfThatIsMoreSmaller() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, String>> actual = emptyIntInt()
                .put(1, 1)
                .put(2, 2)
                .put(3, 3)
                .put(4, 4)
                .zipAll(of("a", "b"), Tuple.of(9, 10), "z");
        final Seq<Tuple2<Tuple2<Object, Object>, String>> expected = Stream.of(Tuple.of(Tuple.of(1, 1), "a"),
                Tuple.of(Tuple.of(2, 2), "b"), Tuple.of(Tuple.of(3, 3), "z"), Tuple.of(Tuple.of(4, 4), "z"));
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldZipAllNonNilsIfThatIsSmaller() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, String>> actual = emptyIntInt()
                .put(1, 1)
                .put(2, 2)
                .put(3, 3)
                .zipAll(this.of("a", "b"), Tuple.of(9, 10), "z");
        final Seq<Tuple2<Tuple2<Object, Object>, String>> expected = Stream.of(Tuple.of(Tuple.of(1, 1), "a"),
                Tuple.of(Tuple.of(2, 2), "b"), Tuple.of(Tuple.of(3, 3), "z"));
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldZipAllNonNilsIfThisIsMoreSmaller() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, String>> actual = emptyIntInt()
                .put(1, 1)
                .put(2, 2)
                .zipAll(of("a", "b", "c", "d"), Tuple.of(9, 10), "z");
        final Seq<Tuple2<Tuple2<Object, Object>, String>> expected = Stream.of(Tuple.of(Tuple.of(1, 1), "a"),
                Tuple.of(Tuple.of(2, 2), "b"), Tuple.of(Tuple.of(9, 10), "c"), Tuple.of(Tuple.of(9, 10), "d"));
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldZipAllNonNilsIfThisIsSmaller() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, String>> actual = emptyIntInt()
                .put(1, 1)
                .put(2, 2)
                .zipAll(of("a", "b", "c"), Tuple.of(9, 10), "z");
        final Seq<Tuple2<Tuple2<Object, Object>, String>> expected = Stream.of(Tuple.of(Tuple.of(1, 1), "a"),
                Tuple.of(Tuple.of(2, 2), "b"), Tuple.of(Tuple.of(9, 10), "c"));
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldZipAllNonNilsOfSameSize() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, String>> actual = emptyIntInt()
                .put(1, 1)
                .put(2, 2)
                .put(3, 3)
                .zipAll(of("a", "b", "c"), Tuple.of(9, 10), "z");
        final Seq<Tuple2<Tuple2<Object, Object>, String>> expected = Stream.of(Tuple.of(Tuple.of(1, 1), "a"),
                Tuple.of(Tuple.of(2, 2), "b"), Tuple.of(Tuple.of(3, 3), "c"));
        assertThat(actual).isEqualTo(expected);
    }

    @Test
    public void shouldZipEmptyAndNonNil() {
        final Seq<Tuple2<Tuple2<Integer, Object>, Integer>> actual = emptyInt().zip(io.vavr.collection.List.of(1));
        assertThat(actual).isEqualTo(Stream.empty());
    }

    // -- getOrElse

    @Test
    public void shouldZipNilWithIndex() {
        assertThat(emptyMap().zipWithIndex()).isEqualTo(Stream.empty());
    }

    // -- partition

    @Test
    public void shouldZipNils() {
        final Seq<Tuple2<Tuple2<Integer, Object>, Object>> actual = emptyInt().zip(io.vavr.collection.List.empty());
        assertThat(actual).isEqualTo(Stream.empty());
    }

    // -- spliterator

    @Test
    public void shouldZipNonEmptyAndNil() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, Object>> actual = emptyIntInt().put(0, 1).zip(io.vavr.collection.List.empty());
        assertThat(actual).isEqualTo(Stream.empty());
    }

    @Test
    public void shouldZipNonNilWithIndex() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, Integer>> actual = emptyIntInt()
                .put(0, 0)
                .put(1, 1)
                .put(2, 2)
                .zipWithIndex();
        assertThat(actual).isEqualTo(
                Stream.of(Tuple.of(Tuple.of(0, 0), 0), Tuple.of(Tuple.of(1, 1), 1), Tuple.of(Tuple.of(2, 2), 2)));
    }

    @Test
    public void shouldZipNonNilsIfThatIsSmaller() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, Integer>> actual = emptyIntInt()
                .put(0, 0)
                .put(1, 1)
                .put(2, 2)
                .zip(io.vavr.collection.List.of(5, 6));
        assertThat(actual).isEqualTo(Stream.of(Tuple.of(Tuple.of(0, 0), 5), Tuple.of(Tuple.of(1, 1), 6)));
    }

    @Test
    public void shouldZipNonNilsIfThisIsSmaller() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, Integer>> actual = emptyIntInt()
                .put(0, 0)
                .put(1, 1)
                .zip(io.vavr.collection.List.of(5, 6, 7));
        assertThat(actual).isEqualTo(Stream.of(Tuple.of(Tuple.of(0, 0), 5), Tuple.of(Tuple.of(1, 1), 6)));
    }

    @Test
    public void shouldZipNonNilsOfSameSize() {
        final Seq<Tuple2<Tuple2<Integer, Integer>, Integer>> actual = emptyIntInt()
                .put(0, 0)
                .put(1, 1)
                .put(2, 2)
                .zip(io.vavr.collection.List.of(5, 6, 7));
        assertThat(actual).isEqualTo(
                Stream.of(Tuple.of(Tuple.of(0, 0), 5), Tuple.of(Tuple.of(1, 1), 6), Tuple.of(Tuple.of(2, 2), 7)));
    }

    @Override
    protected <T> IntMap<T> tabulate(int n, Function<? super Integer, ? extends T> f) {
        io.vavr.collection.Map<Integer, T> map = emptyMap();
        for (int i = 0; i < n; i++) {
            map = map.put(map.size(), f.apply(i));
        }
        return IntMap.of(map);
    }

    @Override
    protected boolean useIsEqualToInsteadOfIsSameAs() {
        return true;
    }

}
