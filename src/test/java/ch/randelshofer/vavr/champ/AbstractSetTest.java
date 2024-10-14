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

import io.vavr.Tuple2;
import io.vavr.collection.HashMap;
import io.vavr.collection.HashMultimap;
import io.vavr.collection.HashSet;
import io.vavr.collection.LinkedHashMap;
import io.vavr.collection.LinkedHashMultimap;
import io.vavr.collection.List;
import io.vavr.collection.Set;
import io.vavr.collection.TreeMap;
import io.vavr.collection.TreeMultimap;
import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Spliterator;
import java.util.concurrent.atomic.AtomicInteger;

public abstract class AbstractSetTest extends AbstractTraversableRangeTest {

    @Override
    abstract protected <T> Set<T> empty();

    abstract protected <T> Set<T> emptyWithNull();

    @Override
    abstract protected <T> Set<T> of(T element);

    @SuppressWarnings("unchecked")
    @Override
    abstract protected <T> Set<T> of(T... elements);

    // -- static narrow

    @Test
    public void shouldAddAllOfIterable() {
        assertThat(of(1, 2, 3).addAll(of(2, 3, 4))).isEqualTo(of(1, 2, 3, 4));
    }

    // -- fill(int, Supplier)

    @Test
    public void shouldAddNonNullAndNull() {
        assertThat(emptyWithNull().add(1).add(null)).contains(null, 1);
    }

    // -- add

    @Test
    public void shouldAddNullAndNonNull() {
        assertThat(emptyWithNull().add(null).add(1)).contains(null, 1);
    }

    @Override
    @Test
    public void shouldBeAwareOfExistingNonUniqueElement() {
        // sets have only distinct elements
    }

    @Test
    public void shouldCalculateDifference() {
        assertThat(of(1, 2, 3).diff(of(2))).isEqualTo(of(1, 3));
        assertThat(of(1, 2, 3).diff(of(5))).isEqualTo(of(1, 2, 3));
        assertThat(of(1, 2, 3).diff(of(1, 2, 3))).isEqualTo(empty());
    }

    // -- addAll

    @Test
    public void shouldCalculateIntersect() {
        assertThat(of(1, 2, 3).intersect(of(2))).isEqualTo(of(2));
        assertThat(of(1, 2, 3).intersect(of(5))).isEqualTo(empty());
        assertThat(of(1, 2, 3).intersect(of(1, 2, 3))).isEqualTo(of(1, 2, 3));
    }

    @Test
    public void shouldCalculateUnion() {
        assertThat(of(1, 2, 3).union(of(2))).isEqualTo(of(1, 2, 3));
        assertThat(of(1, 2, 3).union(of(5))).isEqualTo(of(1, 2, 3, 5));
        assertThat(of(1, 2, 3).union(of(1, 2, 3))).isEqualTo(of(1, 2, 3));
    }

    @Test
    public void shouldHaveDistinctSpliterator() {
        assertThat(of(1, 2, 3).spliterator().hasCharacteristics(Spliterator.DISTINCT)).isTrue();
    }

    @Test
    public void shouldHaveSizedSpliterator() {
        assertThat(of(1, 2, 3).spliterator().hasCharacteristics(Spliterator.SIZED | Spliterator.SUBSIZED)).isTrue();
    }

    // -- diff

    @Test
    public void shouldMapDistinctElementsToOneElement() {
        assertThat(of(1, 2, 3).map(i -> 0)).isEqualTo(of(0));
    }

    @Test
    public void shouldNarrowSet() {
        final Set<Double> doubles = of(1.0d);
        final Set<Number> numbers = Set.narrow(doubles);
        final int actual = numbers.add(new BigDecimal("2.0")).sum().intValue();
        assertThat(actual).isEqualTo(3);
    }

    @Test
    public void shouldNotAddAnExistingElementTwice() {
        final Set<IntMod2> set = of(new IntMod2(2));
        assertThat(set.add(new IntMod2(4))).isSameAs(set);
    }

    // -- equality

    @Test
    public void shouldObeyEqualityConstraints() {

        // sequential collections
        assertThat(empty().equals(io.vavr.collection.HashSet.empty())).isTrue();
        assertThat(of(1).equals(io.vavr.collection.HashSet.of(1))).isTrue();
        assertThat(of(1, 2, 3).equals(io.vavr.collection.HashSet.of(1, 2, 3))).isTrue();
        assertThat(of(1, 2, 3).equals(HashSet.of(3, 2, 1))).isTrue();

        // other classes
        assertThat(empty().equals(List.empty())).isFalse();
        assertThat(empty().equals(HashMap.empty())).isFalse();
        assertThat(empty().equals(HashMultimap.withSeq().empty())).isFalse();

        assertThat(empty().equals(LinkedHashMap.empty())).isFalse();
        assertThat(empty().equals(LinkedHashMultimap.withSeq().empty())).isFalse();

        assertThat(empty().equals(TreeMap.empty())).isFalse();
        assertThat(empty().equals(TreeMultimap.withSeq().empty())).isFalse();
    }

    // -- intersect

    @Test
    public void shouldPartitionInOneIteration() {
        final AtomicInteger count = new AtomicInteger(0);
        final Tuple2<? extends Set<Integer>, ? extends Set<Integer>> results = of(1, 2, 3).partition(i -> {
            count.incrementAndGet();
            return true;
        });
        assertThat(results._1).isEqualTo(of(1, 2, 3));
        assertThat(results._2).isEqualTo(of());
        assertThat(count.get()).isEqualTo(3);
    }

    @Test
    public void shouldRemoveAllElements() {
        assertThat(of(1, 2, 3).removeAll(of(2))).isEqualTo(of(1, 3));
        assertThat(of(1, 2, 3).removeAll(of(5))).isEqualTo(of(1, 2, 3));
    }

    @Test
    public void shouldRemoveElement() {
        assertThat(of(1, 2, 3).remove(2)).isEqualTo(of(1, 3));
        assertThat(of(1, 2, 3).remove(5)).isEqualTo(of(1, 2, 3));
        assertThat(empty().remove(5)).isEqualTo(empty());
    }

    // -- map

    @Override
    @Test
    public void shouldReplaceFirstOccurrenceOfNonNilUsingCurrNewWhenMultipleOccurrencesExist() {
        // sets have only distinct elements
    }

    // -- remove

    @Test
    public void shouldReturnSameSetWhenAddAllContainedElements() {
        final Set<Integer> set = of(1, 2, 3);
        assertThat(set.addAll(of(1, 2, 3))).isSameAs(set);
    }

    // -- partition

    @Test
    public void shouldReturnSameSetWhenAddAllEmptyToNonEmpty() {
        final Set<Integer> set = of(1, 2, 3);
        assertThat(set.addAll(empty())).isSameAs(set);
    }

    // -- removeAll

    @Test
    public void shouldReturnSameSetWhenAddAllNonEmptyToEmpty() {
        final Set<Integer> set = of(1, 2, 3);
        if (set.isOrdered()) {
            assertThat(empty().addAll(set)).isEqualTo(set);
        } else {
            assertThat(empty().addAll(set)).isSameAs(set);
        }
    }

    @Test
    public void shouldReturnSameSetWhenEmptyDiffNonEmpty() {
        final Set<Integer> empty = empty();
        assertThat(empty.diff(of(1, 2))).isSameAs(empty);
    }

    @Test
    public void shouldReturnSameSetWhenEmptyIntersectNonEmpty() {
        final Set<Integer> empty = empty();
        assertThat(empty.intersect(of(1, 2))).isSameAs(empty);
    }

    // -- union

    @Test
    public void shouldReturnSameSetWhenEmptyRemoveAllNonEmpty() {
        final Set<Integer> empty = empty();
        assertThat(empty.removeAll(of(1, 2, 3))).isSameAs(empty);
    }

    @Test
    public void shouldReturnSameSetWhenEmptyUnionNonEmpty() {
        final Set<Integer> set = of(1, 2);
        if (set.isOrdered()) {
            assertThat(empty().union(set)).isEqualTo(set);
        } else {
            assertThat(empty().union(set)).isSameAs(set);
        }
    }

    @Test
    public void shouldReturnSameSetWhenNonEmptyDiffEmpty() {
        final Set<Integer> set = of(1, 2);
        assertThat(set.diff(empty())).isSameAs(set);
    }

    // disabled tests

    @Test
    public void shouldReturnSameSetWhenNonEmptyIntersectEmpty() {
        final Set<Integer> set = of(1, 2);
        final Set<Integer> empty = empty();
        if (set.isOrdered()) {
            assertThat(set.intersect(empty)).isEqualTo(empty);
        } else {
            assertThat(set.intersect(empty)).isSameAs(empty);
        }
    }

    @Test
    public void shouldReturnSameSetWhenNonEmptyRemoveAllEmpty() {
        final Set<Integer> set = of(1, 2, 3);
        assertThat(set.removeAll(empty())).isSameAs(set);
    }

    // -- spliterator

    @Test
    public void shouldReturnSameSetWhenNonEmptyUnionEmpty() {
        final Set<Integer> set = of(1, 2);
        assertThat(set.union(empty())).isSameAs(set);
    }

    @Test
    public void shouldReturnSingleAfterFillWithConstant() {
        assertThat(fill(17, () -> 7))
                .hasSize(1)
                .isEqualTo(of(7));
    }

    @Test
    public void shouldReturnSizeWhenSpliterator() {
        assertThat(of(1, 2, 3).spliterator().getExactSizeIfKnown()).isEqualTo(3);
    }
}
