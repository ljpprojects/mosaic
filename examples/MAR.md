# Mosaic Async Runtime

The Mosaic Async Runtime (MAR) is the async runtime bundled with `std` designed
for use with Mosaic.

THIS SI WORK IN PROGRESS

## Tasks

A task in Mosaic will implement `std::async::Future<T>`. The definition of this
interface is similar to this:

```
interface Future<T> : msr::Ref, marker::StackCompat, ... {
  fn poll(&instancetype, waker: &.Waker) -> data::Maybe<T> @allocates;
}
```

The `poll` method should check with the internal state of the `Future` to see if
a result is ready to be returned. If a result is ready and the task has finished,
`poll` should return `data::Maybe::Some`. If the task is not finished then `poll`
should return `data::Maybe::None` and the waker should be cloned and escaped into
the internal state of the `Future` so that when the task is ready to make progress
it can call `Waker::wake`.

Once `poll` returns `Maybe::Some` once it should continue to return `Maybe::Some`
with the same value.

## Async functions

Almost exactly like Rust, when you declare an `@async` function, the compiler
will turn it into a state machine that implements `Future`.

```
fn fetchY -> i32 @async {
  ...
}

fn fetchZ -> i32 @async {
  ...
}

fn addAsync(x: i32) -> i32 @async {
  let y = await fetchY();
  let z = await fetchZ();
  return x + y + z;
}
```

```
enum _8addAsyncw_w_state {
  # This is the starting state
  case Start { x: i32 }; # Arguments are in this variant
  
  # At this point we have x, and we are waiting on fetchY
  case Waiting0_6fetchYw { x: i32, fut: &_6fetchYw_future };
  
  # By this point y has been resolved and we are waiting on fetchZ
  case Waiting1_6fetchZw { x: i32, y: i32, fut: &_6fetchZw_future };
  
  # Now fetchZ has resolved, so we do the computations and are done
  case Done(i32);
}

interface _8addAsyncw_w_future : async::Future<i32>, marker::StackCompat, async::Escapeable {
  mut state: _8addAsyncw_w_state;
  
  fn new(x: i32) -> &instancetype @public;
}

impl _8addAsyncw_w_future {
  fn new(x: i32) -> &instancetype @public {
    let self = core::mem::alloc(sizeof instancetype);
    self._state = _8addAsyncw_w_state::Start(x);
    return self;
  }

  fn Future::poll(self: &instancetype, waker: &.Waker) -> data::Maybe<T> @allocates {
    # Since this is in a loop it moves to the next state if the match doesn't
    # return None
    while true {
        match self {
        # If there were computations before that first await it would be here
        # Move into the next state with the new future
        case Start { x } ->
          self._state = _8addAsyncw_w_state::Waiting0_6fetchYw(x, _6fetchYw_future::new()),
        case Waiting0_6fetchYw { x, fut } -> match fut.poll(waker.clone()) {
          case Some(y) ->
            self._state = _8addAsyncw_w_state::Waiting1_6fetchZw(x, y, _6fetchXw_future::new()),
          case None -> return data::Maybe::None;
        },
        case Waiting1_6fetchZw { x, y, fut } -> match fut.poll(waker.clone()) {
          case Some(z) ->
            self._state = _8addAsyncw_w_state::Done(x + y + z),
          case None -> return data::Maybe::None;
        },
        case Done(result) -> return data::Maybe::some(result),
      }
    }
  }
}
```