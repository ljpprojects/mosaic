@0xa14c10b6f77b208b;

struct PackageMeta {
    id @3 :UInt64;
    name @0 :Text;

    version @1 :UInt16;
    authors @2 :List(Text);
    compilationFlags @4 :List(Text);

    kind :union {
        binary @5 :Text; # the text stores the generated binary's name
        library @6 :LibraryMeta;
    }

    repo :union {
        some @7 :Text;
        none @8 :Void;
    }
}

struct LibraryMeta {
    dependencies @0 :List(UInt64);
}