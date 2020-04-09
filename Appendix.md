
## Performance 
Performance is important because proof-reader might be run multiple times during a single proof-editing session, and the editing experience would be affected by slow feedback.  The average length of a student submission is between a few hundred to a few thousand lines of code. For example, acceptance3-week-05_mystery-functions_anonymized.v is about 2000 lines of code. Its performance: 

    preprocess took: 0.0050 seconds.
    construct_node took: 0.0791 seconds.
    check_arity took: 0.0024 seconds.
    overall took: 0.0868 seconds.

This is an acceptable speed for most use cases. Clearly, construct_node takes up the majority of time. For my performance test I run proof-reader on perf1.v which is 50000 lines of code (repeated copies of acceptance3): 

    preprocess took: 0.0847 seconds.
    construct_node took: 10.9696 seconds.
    check_arity took: 0.0777 seconds.
    overall took: 11.1329 seconds.

While such long inputs are unlikely to occur in practical use, this is undesirable given our theoretical estimate of time complexity of O(N),  since the input increased by a factor of 25 but the overall time increased by a factor of 125 times. I hypothesize that this is due to the overhead of creating Node objects, manipulating long strings, and perhaps the overhead of hundreds of thousands of recursive calls, since Python's parameters are pass-by-value. Performance optimization strategies are discussed in "Potential Improvements".
