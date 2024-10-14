package ch.randelshofer.vavr.champ;

import io.vavr.Tuple2;
import io.vavr.Value;
import io.vavr.collection.Iterator;
import io.vavr.collection.Map;
import io.vavr.collection.Traversable;

import java.util.Collection;
import java.util.Objects;
import java.util.function.Function;

class ValueModule {
    private ValueModule() {
    }

    static <T, R extends Traversable<T>> R toTraversable(Value<T> value, R empty, Function<T, R> ofElement, Function<Iterable<T>, R> ofAll) {
        if (value.isEmpty()) {
            return empty;
        } else {
            return (R) (value.isSingleValued() ? (Traversable) ofElement.apply(value.get()) : (Traversable) ofAll.apply(value));
        }
    }

    static <T, K, V, E extends Tuple2<? extends K, ? extends V>, R extends Map<K, V>> R toMap(Value<T> value, R empty, Function<E, R> ofElement, Function<Iterable<E>, R> ofAll, Function<? super T, ? extends E> f) {
        if (value.isEmpty()) {
            return empty;
        } else {
            return (R) (value.isSingleValued() ? (Map) ofElement.apply((E) f.apply(value.get())) : (Map) ofAll.apply(Iterator.ofAll(value).map(f)));
        }
    }

    static <T, R extends Collection<T>> R toJavaCollection(Value<T> value, Function<Integer, R> containerSupplier) {
        return toJavaCollection(value, containerSupplier, 16);
    }

    static <T, R extends Collection<T>> R toJavaCollection(Value<T> value, Function<Integer, R> containerSupplier, int defaultInitialCapacity) {
        int size;
        if (value instanceof Traversable && ((Traversable) value).isTraversableAgain() && !value.isLazy()) {
            size = ((Traversable) value).size();
        } else {
            size = defaultInitialCapacity;
        }

        R container = (R) containerSupplier.apply(size);
        Objects.requireNonNull(container);
        value.forEach(container::add);
        return container;
    }
}
