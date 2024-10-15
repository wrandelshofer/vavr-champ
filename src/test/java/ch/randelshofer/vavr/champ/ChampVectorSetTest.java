package ch.randelshofer.vavr.champ;

import io.vavr.collection.List;
import io.vavr.collection.Set;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Spliterator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collector;

public class ChampVectorSetTest extends AbstractSetTest {

    @Override
    protected <T> Collector<T, ArrayList<T>, ChampVectorSet<T>> collector() {
        return ChampVectorSet.collector();
    }

    @Override
    protected <T> ChampVectorSet<T> empty() {
        return ChampVectorSet.empty();
    }

    @Override
    protected <T> ChampVectorSet<T> emptyWithNull() {
        return empty();
    }

    @Override
    protected <T> ChampVectorSet<T> fill(int n, Supplier<? extends T> s) {
        return ChampVectorSet.fill(n, s);
    }

    @Override
    protected int getPeekNonNilPerformingAnAction() {
        return 1;
    }

    @Override
    protected <T> ChampVectorSet<T> of(T element) {
        return ChampVectorSet.of(element);
    }

    @SuppressWarnings("varargs")
    @SafeVarargs
    @Override
    protected final <T> ChampVectorSet<T> of(T... elements) {
        return ChampVectorSet.of(elements);
    }

    @Override
    protected <T> ChampVectorSet<T> ofAll(Iterable<? extends T> elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Boolean> ofAll(boolean... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Byte> ofAll(byte... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Character> ofAll(char... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Double> ofAll(double... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Float> ofAll(float... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Integer> ofAll(int... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Long> ofAll(long... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected ChampVectorSet<Short> ofAll(short... elements) {
        return ChampVectorSet.ofAll(elements);
    }

    @Override
    protected <T extends Comparable<? super T>> ChampVectorSet<T> ofJavaStream(java.util.stream.Stream<? extends T> javaStream) {
        return ChampVectorSet.ofAll(javaStream);
    }

    @Override
    protected ChampVectorSet<Character> range(char from, char toExclusive) {
        return ChampVectorSet.range(from, toExclusive);
    }

    @Override
    protected ChampVectorSet<Integer> range(int from, int toExclusive) {
        return ChampVectorSet.range(from, toExclusive);
    }

    @Override
    protected ChampVectorSet<Long> range(long from, long toExclusive) {
        return ChampVectorSet.range(from, toExclusive);
    }

    @Override
    protected ChampVectorSet<Character> rangeBy(char from, char toExclusive, int step) {
        return ChampVectorSet.rangeBy(from, toExclusive, step);
    }

    @Override
    protected ChampVectorSet<Double> rangeBy(double from, double toExclusive, double step) {
        return ChampVectorSet.rangeBy(from, toExclusive, step);
    }

    @Override
    protected ChampVectorSet<Integer> rangeBy(int from, int toExclusive, int step) {
        return ChampVectorSet.rangeBy(from, toExclusive, step);
    }

    @Override
    protected ChampVectorSet<Long> rangeBy(long from, long toExclusive, long step) {
        return ChampVectorSet.rangeBy(from, toExclusive, step);
    }

    @Override
    protected ChampVectorSet<Character> rangeClosed(char from, char toInclusive) {
        return ChampVectorSet.rangeClosed(from, toInclusive);
    }

    @Override
    protected ChampVectorSet<Integer> rangeClosed(int from, int toInclusive) {
        return ChampVectorSet.rangeClosed(from, toInclusive);
    }

    @Override
    protected ChampVectorSet<Long> rangeClosed(long from, long toInclusive) {
        return ChampVectorSet.rangeClosed(from, toInclusive);
    }

    @Override
    protected ChampVectorSet<Character> rangeClosedBy(char from, char toInclusive, int step) {
        return ChampVectorSet.rangeClosedBy(from, toInclusive, step);
    }

    @Override
    protected ChampVectorSet<Double> rangeClosedBy(double from, double toInclusive, double step) {
        return ChampVectorSet.rangeClosedBy(from, toInclusive, step);
    }

    @Override
    protected ChampVectorSet<Integer> rangeClosedBy(int from, int toInclusive, int step) {
        return ChampVectorSet.rangeClosedBy(from, toInclusive, step);
    }

    @Override
    protected ChampVectorSet<Long> rangeClosedBy(long from, long toInclusive, long step) {
        return ChampVectorSet.rangeClosedBy(from, toInclusive, step);
    }

    @Test
    public void shouldHaveOrderedSpliterator() {
        assertThat(of(1, 2, 3).spliterator().hasCharacteristics(Spliterator.ORDERED)).isTrue();
    }

    @Test
    public void shouldKeepOrder() {
        final List<Integer> actual = ChampVectorSet.<Integer>empty().add(3).add(2).add(1).toList();
        assertThat(actual).isEqualTo(List.of(3, 2, 1));
    }

    @Test
    public void shouldNarrowLinkedHashSet() {
        final ChampVectorSet<Double> doubles = of(1.0d);
        final ChampVectorSet<Number> numbers = ChampVectorSet.narrow(doubles);
        final int actual = numbers.add(new BigDecimal("2.0")).sum().intValue();
        assertThat(actual).isEqualTo(3);
    }

    // -- static narrow

    @Test
    public void shouldNotHaveSortedSpliterator() {
        assertThat(of(1, 2, 3).spliterator().hasCharacteristics(Spliterator.SORTED)).isFalse();
    }

    // -- replace

    @Test
    public void shouldPreserveOrderWhenReplacingExistingElement() {
        final Set<Integer> set = ChampVectorSet.of(1, 2, 3);
        final Set<Integer> actual = set.replace(2, 0);
        final Set<Integer> expected = ChampVectorSet.of(1, 0, 3);
        assertThat(actual).isEqualTo(expected);
        Assertions.assertThat(List.ofAll(actual)).isEqualTo(List.ofAll(expected));
    }

    @Test
    public void shouldPreserveOrderWhenReplacingExistingElementAndRemoveOtherIfElementAlreadyExists() {
        final Set<Integer> set = ChampVectorSet.of(1, 2, 3, 4, 5);
        final Set<Integer> actual = set.replace(2, 4);
        final Set<Integer> expected = ChampVectorSet.of(1, 4, 3, 5);
        assertThat(actual).isEqualTo(expected);
        Assertions.assertThat(List.ofAll(actual)).isEqualTo(List.ofAll(expected));
    }

    @Test
    public void shouldReturnSameInstanceIfReplacingNonExistingElement() {
        final Set<Integer> set = ChampVectorSet.of(1, 2, 3);
        final Set<Integer> actual = set.replace(4, 0);
        assertThat(actual).isSameAs(set);
    }

    @Test
    public void shouldReturnSameInstanceWhenReplacingExistingElementWithIdentity() {
        final Set<Integer> set = ChampVectorSet.of(1, 2, 3);
        final Set<Integer> actual = set.replace(2, 2);
        assertThat(actual).isSameAs(set);
    }

    // -- transform

    @Test
    @Disabled("WR this does not work because our instance is different from the one in io.vavr")
    public void shouldReturnSelfOnConvertToLinkedSet() {
        final ChampVectorSet<Integer> value = of(1, 2, 3);
        assertThat(value.toLinkedSet()).isSameAs(value);
    }

    // -- toLinkedSet

    @Test
    public void shouldReturnTrueWhenIsSequentialCalled() {
        assertThat(of(1, 2, 3).isSequential()).isTrue();
    }

    // -- spliterator

    @Test
    public void shouldTransform() {
        final String transformed = of(42).transform(v -> String.valueOf(v.get()));
        assertThat(transformed).isEqualTo("42");
    }

    @Override
    protected <T> ChampVectorSet<T> tabulate(int n, Function<? super Integer, ? extends T> f) {
        return ChampVectorSet.tabulate(n, f);
    }

    // -- isSequential()

    @Override
    protected boolean useIsEqualToInsteadOfIsSameAs() {
        return false;
    }

}
