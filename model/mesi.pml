/* Formal Verification of the MESI cache coherence protocol in Spin/Promela.
 * Copyright (C) 2023  Luke Marzen
 */


/* Configuration Parameters
 */
#define NPROC       4  // Number of caching agents (i.e. Processors/CPUs)
#define CACHE_SIZE  1  // Size of each cache, Capacity in Bytes
#define MEMORY_SIZE 2  // Size of main memory, Capacity in Bytes

/* The following options determine whether the corresponding LTL formulas are
 * compiled.
 */
#define ENABLE_VERIF_LTL 1 // Enable compilation of verification LTL
#define ENABLE_VALID_LTL 1 // Enable compilation of validation LTL

/* Note on mtype. mtype is effectively just repeated #define that starts
 * numbering at 1 not 0. This makes it less useful as spin initializes
 * everything to 0 by default.
 */

/* Cache Line States
 */
#define INVALID 0
#define SHARED 1
#define EXCLUSIVE 2
#define MODIFIED 3

/* Processor Requests
 */
#define PR_RD 0
#define PR_WR 1

/* Bus Side Requests
 */
#define NONE      0
#define BUS_RD    1
#define BUS_RDX   2
#define BUS_UPGR  3
#define FLUSH     4
#define FLUSH_OPT 5 // for simplicity, cache to cache transfer has not been
                    // implemented, so we don't need this.


/* Uses tricks with atomic regions to reduce state space without altering the
 * behavior that we are interested in verifying.
 *
 * Outlined in this 2007 article by Paul McKenney:
 * <https://lwn.net/Articles/243851/>
 */
#define REDUCE_WITH_ATOMIC 1

/* Enforce a deterministic bus acknowledgment ordering. This substantially
 * reduces statespace for configurations with more than 2 processors.
 */
#define DETERMINISTIC_BUS_ACKS 1

/* This optimization eliminates data storage from the model significantly
 * reducing statespace while degrading the completeness of validation.
 */
#define EXCLUDE_DATA_STORAGE 1

/* Macros for cache line operations in a direct mapped cache
 * (i.e. associativity = 1).
 * 'addr' is the address in main memory.
 */
#define CALC_CACHE_LINE(addr) \
    (addr & (CACHE_SIZE - 1))

#define GET_STATE(addr) \
    (CACHES[_pid].lines[CALC_CACHE_LINE(addr)].state)

#define SET_STATE(addr, s) \
    CACHES[_pid].lines[CALC_CACHE_LINE(addr)].state = (s)

#define GET_TAG(addr) \
    (CACHES[_pid].lines[CALC_CACHE_LINE(addr)].tag)

#define SET_TAG(addr) \
    CACHES[_pid].lines[CALC_CACHE_LINE(addr)].tag = (addr)

#define GET_DATA(addr) \
    (CACHES[_pid].lines[CALC_CACHE_LINE(addr)].data)

#define SET_DATA(addr, val) \
    CACHES[_pid].lines[CALC_CACHE_LINE(addr)].data = (val)

/* Macros for expanding macros before python preprocessing step.
 *
 * __EXPAND_SELECT__ is a macro that creates a non-deterministic selection using
 * an if statement which is avoids the increased state space depth incurred when
 * using the select statement. From my experiments reducing depth this way
 * drastically reduces verification time and space requirements.
 */
#define __EXPAND_SELECT__(var, lower, upper) \
    ::__EXPAND_SELECT__(                     \
        var,                                 \
        lower,                               \
        upper                                \
    )

/* Data structure representing a cache line.
 * Note: Using a basic direct mapped cache.
 *   |       Cache Line      |
 *   | State |  Tag  | Data  |
 */
typedef cache_line_t {
    byte state;
    byte tag;
#if !EXCLUDE_DATA_STORAGE
    byte data;
#endif
}

/* Data structure representing a single cache.
 *             Cache
 *   | State |  Tag  | Data  | --
 *   | State |  Tag  | Data  |   \  CACHE_SIZE
 *   | State |  Tag  | Data  |   /  ex: 4 lines
 *   | State |  Tag  | Data  | --
 */
typedef cache_t {
    cache_line_t lines[CACHE_SIZE];
}

/* Data structure representing a load/store instruction.
 */
typedef ldst_inst_t {
    byte op;   // load/store. Indicated by PR_RD/PR_WR.
    byte addr; // source/destination memory address
#if !EXCLUDE_DATA_STORAGE
    byte val;  // only used for store instruction
#endif
}

/* Data structure representing a bus message.
 */
typedef message_t {
    byte op;
    byte addr;
    // this will later need value for cache-to-cache transfer
}

/* Data structure representing a global bus that connects each processor.
 */
typedef bus_t {
    bool locked; // mutex
    byte op;
    byte addr;
#if DETERMINISTIC_BUS_ACKS
    byte ack; // keeps track of acknowledgments
#elif NPROC <= 8
    byte ack;
#elif NPROC <= 16
    short ack;
#elif NPROC <= 32
    int ack;
#endif
}

/* Global caches.
 * Each processor has its own cache. The processor id (_pid) is used to index
 * the array.
 * An important assumption is made here; Caches are symmetric.
 */
cache_t CACHES[NPROC];

/* Global byte array representing Main Memory.
 */ 
#if !EXCLUDE_DATA_STORAGE
byte MAIN_MEMORY[MEMORY_SIZE];
#endif

/* Global bus connecting each processor.
 */
bus_t BUS;


/* Non-deterministically select a load/store instruction instruction to execute.
 *
 * Operation  inst.op    {PR_RD, PR_WR} (Load/Store)
 * Address    inst.addr  [0, MEMORY_SIZE)
 * Value      inst.val   [0, 1]
 */
inline select_new_instruction() {
    if
    :: inst.op = PR_RD;
#if !EXCLUDE_DATA_STORAGE
       // arbitrarily constraining val to 0 since it is unused by this operation
       // and constraining it cuts state space in half.
       inst.val = 0;
#endif
    :: inst.op = PR_WR;
#if !EXCLUDE_DATA_STORAGE
        if
        // We store just two values since this is enough to check if there are
        // any violations of the protocol. Obviously in a real world system you
        // would have must larger word sizes.
        :: inst.val = 0;
        :: inst.val = 1;
        fi
#endif
    fi

    // Generating a number in a range without state space explosion is
    // a challenging task in promela. Initially I used the select keyword
    // provided for this purpose... select(addr: 0 .. MEMORY_SIZE - 1)
    // However select is effectively a find and replace macro that uses a do
    // loop which causes an exponential state space explosion. Using an if
    // statement is orders of magnitudes more efficient in terms of state space
    // size and verification time. Unfortunately, promela does not provide a
    // simple abstraction for creating these if statements based on a range
    // known at compile-time.
    // The solution I have implemented is to pre-process this file with a python
    // script that will create an if statement that achieves the desired effect.
    // if
    // :: inst.addr = 0;
    // :: inst.addr = 1;
    // ...
    // :: inst.addr = MEMORY_SIZE - 1;
    // fi
    __EXPAND_SELECT__(inst.addr, 0, MEMORY_SIZE - 1)
}

/* Updates 'message' with the information that must be broadcasted the other
 * processors to inform them how they must update their state. The bus operation
 * is decided based on the operation of the processor's current executing
 * instruction as well as the current state of the cache.
 * See table 1.2 <https://en.wikipedia.org/wiki/MESI_protocol#Operation>
 */
inline prepare_message() {
    message.addr = inst.addr;
    if
    :: GET_TAG(inst.addr) != inst.addr ->
        // Tag not found in cache.
        if
        :: GET_STATE(inst.addr) == MODIFIED ->
            message.op = FLUSH;
            message.addr = GET_TAG(inst.addr);
        :: else ->
            if
            :: inst.op == PR_RD -> message.op = BUS_RD;
            :: inst.op == PR_WR -> message.op = BUS_RDX;
            fi
        fi
    :: GET_TAG(inst.addr) == inst.addr ->
        // Tag found in cache.
        if
        :: GET_STATE(inst.addr) == INVALID ->
            if
            :: inst.op == PR_RD -> message.op = BUS_RD;
            :: inst.op == PR_WR -> message.op = BUS_RDX;
            fi
        :: GET_STATE(inst.addr) == SHARED ->
            if
            :: inst.op == PR_RD -> message.op = NONE;
            :: inst.op == PR_WR -> message.op = BUS_UPGR;
            fi
        :: GET_STATE(inst.addr) == EXCLUSIVE -> message.op = NONE;
        :: GET_STATE(inst.addr) == MODIFIED -> message.op = NONE;
        fi
    fi
}

/* Preform the cache operation that we told other processors that we were going
 * to preform.
 * See tables 1.1 & 1.2 <https://en.wikipedia.org/wiki/MESI_protocol#Operation>
 */
inline update_cache_state() {
    atomic {
        if
        :: message.op == BUS_RD  ->
            SET_STATE(message.addr, SHARED);
            SET_TAG(message.addr);
#if !EXCLUDE_DATA_STORAGE
            SET_DATA(message.addr, MAIN_MEMORY[message.addr]);
#endif
        :: message.op == BUS_RDX ->
            SET_STATE(message.addr, EXCLUSIVE);
            SET_TAG(message.addr);
#if !EXCLUDE_DATA_STORAGE
            SET_DATA(message.addr, MAIN_MEMORY[message.addr]);
#endif
        :: message.op == BUS_UPGR ->
            SET_STATE(message.addr, EXCLUSIVE);
        :: message.op == FLUSH ->
            SET_STATE(message.addr, SHARED);
#if !EXCLUDE_DATA_STORAGE
            MAIN_MEMORY[message.addr] = GET_DATA(message.addr);
#endif
        fi
    }
}

/* This subroutine is responsible for 'snooping' on the bus.
 * The processor will read the bus, preform the correct response, and send an
 * acknowledgment.
 * See table 1.2 <https://en.wikipedia.org/wiki/MESI_protocol#Operation>
*/
inline snoop_bus() {
    // We only need to preform an action if the data is in our cache and not
    // invalid.
    if
    :: GET_TAG(BUS.addr) == BUS.addr && GET_STATE(BUS.addr) != INVALID ->
        // Disallowed transition. Another processor should not flush data if we
        // have a valid data. A processor only flushes data when it has modified
        // it, thus all other processor's with this tag would have an invalid
        // copy.
        assert(BUS.op != FLUSH);

#if !EXCLUDE_DATA_STORAGE
        if
        :: GET_STATE(BUS.addr) == MODIFIED ->
            MAIN_MEMORY[BUS.addr] = GET_DATA(BUS.addr);
        :: else -> skip;
        fi
#endif

        if
        :: BUS.op == BUS_RD -> SET_STATE(BUS.addr, SHARED);
        :: BUS.op == BUS_RDX -> SET_STATE(BUS.addr, INVALID);
        :: BUS.op == BUS_UPGR -> SET_STATE(BUS.addr, INVALID);
        fi
    :: else -> skip;
    fi

    prepare_message();
#if !DETERMINISTIC_BUS_ACKS
    BUS.ack = BUS.ack | (1 << _pid);
#else
    BUS.ack = BUS.ack + 1;
#endif
}

/* Each process represents a processor/CPU.
 */
active[NPROC] proctype proc() {
    // bit-set used for comparison to determine when all acknowledgments have
    // been received.
#if !DETERMINISTIC_BUS_ACKS
#if NPROC <= 8
    byte received_all_acks  = (((1 << NPROC) - 1) & ~(1 << _pid));;
#elif NPROC <= 16
    short received_all_acks = (((1 << NPROC) - 1) & ~(1 << _pid));;
#elif NPROC <= 32
    int received_all_acks   = (((1 << NPROC) - 1) & ~(1 << _pid));;
#endif
#endif

    ldst_inst_t inst;
    message_t message;

#if REDUCE_WITH_ATOMIC
    atomic {
#endif
    select_new_instruction();
    prepare_message();
#if REDUCE_WITH_ATOMIC
    }
#endif

    do
        :: message.op == NONE ->
            // This operation does not require communication. Perform it now.
#if REDUCE_WITH_ATOMIC
            atomic {
#endif
            if
            :: inst.op == PR_RD ->
#if !EXCLUDE_DATA_STORAGE
                // The data we are reading from the cache should be the same as
                // the value in main memory unless we have modified it.
                assert(GET_DATA(inst.addr) == MAIN_MEMORY[inst.addr]
                       || GET_STATE(inst.addr) == MODIFIED);
#else
                skip;
#endif
            :: inst.op == PR_WR ->
                SET_STATE(inst.addr, MODIFIED);
#if !EXCLUDE_DATA_STORAGE
                SET_DATA(inst.addr, inst.val);
#endif
            fi

            select_new_instruction();
            prepare_message();

            // Check whether we need to do anything to unblock another processor
            // by listening on the bus.
            if
#if !DETERMINISTIC_BUS_ACKS
            :: BUS.locked && !(BUS.ack & (1 << _pid)) ->
#else
            :: BUS.locked && BUS.ack == _pid ->
#endif
                snoop_bus();
            :: else -> skip;
            fi
#if REDUCE_WITH_ATOMIC
            }
#endif
        :: message.op != NONE ->
            // To execute our operation we need to issue a bus side request.
            if
            // Bus is available, lock bus, and broadcast our message.
            :: atomic {
                    !BUS.locked;
                    BUS.locked = true;
                    // Publish message on the bus.
                    BUS.op = message.op;
                    BUS.addr = message.addr;
                }

                // Wait for all other processors to acknowledge
                do
#if REDUCE_WITH_ATOMIC
#if !DETERMINISTIC_BUS_ACKS
                :: atomic { BUS.ack != received_all_acks ->
                    skip; }
#else
                :: atomic { BUS.ack != NPROC ->
                    skip; }
                :: atomic { BUS.ack == _pid ->
                    BUS.ack = BUS.ack + 1; }
#endif
#else
#if !DETERMINISTIC_BUS_ACKS
                :: BUS.ack != received_all_acks ->
                    skip;
#else
                :: BUS.ack != NPROC ->
                    skip;
                :: BUS.ack == _pid ->
                    BUS.ack = BUS.ack + 1;
#endif
#endif
                :: else ->
                    break;
                od

#if REDUCE_WITH_ATOMIC
                atomic {
#endif
                update_cache_state();
                prepare_message();
                atomic {
                    BUS.ack = 0;
                    BUS.locked = false;
                }
#if REDUCE_WITH_ATOMIC
                }
#endif
            // Bus is unavailable, if we haven't listen yet, do so now, else we
            // are blocked.
#if REDUCE_WITH_ATOMIC
#if !DETERMINISTIC_BUS_ACKS
            :: atomic { BUS.locked && !(BUS.ack & (1 << _pid));
#else
            :: atomic { BUS.locked && BUS.ack == _pid;
#endif
                snoop_bus(); }
#else
#if !DETERMINISTIC_BUS_ACKS
            :: BUS.locked && !(BUS.ack & (1 << _pid));
#else
            :: BUS.locked && BUS.ack == _pid;
#endif
                snoop_bus();
#endif
            fi
    od
}


/* ----------------------------- VERIFICATION ----------------------------------
 *
 * For any given pair of caches, the permitted states of a given cache line are
 * as follows:
 *        M   E   S   I
 *     M  X   X   X   ✓
 *     E  X   X   X   ✓
 *     S  X   X   ✓   ✓
 *     I  ✓   ✓   ✓   ✓
 *
 * It is non-trivial to express a statement in spin that expresses the
 * following...
 *   forall i,j such that i != j, ...
 * This poses the challenge, how do we dynamically express that the above table
 * of permitted states holds for all states?
 * To address this and avoid enumerating every possible combination for every
 * cache line we make the following assumption,
 * Assumption: Caches are symmetrical.
 * Therefore if there is an permitted state violation between any two caches the
 * same violation exists between every other combination of caches.
 * Hence it suffices to show that no violations exist between the first and
 * second cache.
 *
 * The ENABLE_VERIF_LTL macro enables the compilation of the related LTL.
 */

#if ENABLE_VERIF_LTL
/* LTL statement that verifies the permitted states of described in the table
 * above.
 * This statement is long, but enables everything to be verified in a single
 * pass. I have broken this into 3 smaller LTL statements further in this file.
 */
ltl permitted_states {
    [] ( ((CACHES[0].lines[0].tag) == (CACHES[1].lines[0].tag)) ->
        (
            ((CACHES[0].lines[0].state == MODIFIED) ->
                (CACHES[1].lines[0].state == INVALID))
         && ((CACHES[0].lines[0].state == EXCLUSIVE) ->
                (CACHES[1].lines[0].state == INVALID))
         && ((CACHES[0].lines[0].state == SHARED) ->
                ((CACHES[1].lines[0].state == SHARED)
              || (CACHES[1].lines[0].state == INVALID)))
//       && ((CACHES[0].lines[0].state == INVALID) -> true)

         && ((CACHES[1].lines[0].state == MODIFIED) ->
                (CACHES[0].lines[0].state == INVALID))
         && ((CACHES[1].lines[0].state == EXCLUSIVE) ->
                (CACHES[0].lines[0].state == INVALID))
         && ((CACHES[1].lines[0].state == SHARED) ->
                ((CACHES[0].lines[0].state == SHARED)
              || (CACHES[0].lines[0].state == INVALID)))
//       && ((CACHES[1].lines[0].state == INVALID) -> true)
        )
    )
}

/* If a cache line exists in two caches and is MODIFIED in one cache then it is
 * INVALID in the other caches.
 */
 ltl modified_implies_others_invalid {
    [] ( ((CACHES[0].lines[0].tag) == (CACHES[1].lines[0].tag)) ->
        (
            ((CACHES[0].lines[0].state == MODIFIED) ->
                (CACHES[1].lines[0].state == INVALID))
         && ((CACHES[1].lines[0].state == MODIFIED) ->
                (CACHES[0].lines[0].state == INVALID))
        )
    )
}

/* If a cache line exists in two caches and is EXCLUSIVE in one cache then it is
 * INVALID in the other caches.
 */
ltl exclusive_implies_others_invalid {
    [] ( ((CACHES[0].lines[0].tag) == (CACHES[1].lines[0].tag)) ->
        (
            ((CACHES[0].lines[0].state == EXCLUSIVE) ->
                (CACHES[1].lines[0].state == INVALID))
         && ((CACHES[1].lines[0].state == EXCLUSIVE) ->
                (CACHES[0].lines[0].state == INVALID))
        )
    )
}

/* If a cache line exists in two caches and is SHARED in one cache then it is
 * SHARED or INVALID in the other caches.
 */
ltl shared_implies_others_shared_or_invalid {
    [] ( ((CACHES[0].lines[0].tag) == (CACHES[1].lines[0].tag)) ->
        (
            ((CACHES[0].lines[0].state == SHARED) ->
                ((CACHES[1].lines[0].state == SHARED)
              || (CACHES[1].lines[0].state == INVALID)))
         && ((CACHES[1].lines[0].state == SHARED) ->
                ((CACHES[0].lines[0].state == SHARED)
              || (CACHES[0].lines[0].state == INVALID)))
        )
    )
}
#endif


/* ------------------------------ VALIDATION -----------------------------------
 *
 * To validate this model I have created LTL statements below which prove that
 * there exists a trace in which data is eventually written to memory and also
 * that there exists a trace where data is written data is eventually written to
 * each cache. We also validate that there exists a trace where a cache line can
 * eventually reach each of the MESI states. To do this, LTL has been written
 * that expresses that what we want to show cannot happen, thus if there is a
 * violation of the LTL formula then a valid path does exist thus validating
 * that our model enables the behavior we are interested.
 *
 * More validation exists in the model itself through assert statements.
 *
 * Additionally we validate the configuration parameters. This prevents user
 * error.
 *
 * The ENABLE_VALID_LTL macro enables the compilation of the related LTL.
 */

#if ENABLE_VALID_LTL

/* A counterexample to this LTL formula proves that that there exists a trace
 * in which data in memory will eventually be altered.
 */
#if !EXCLUDE_DATA_STORAGE
ltl validate_memory {
    ! (
        <>(MAIN_MEMORY[0] == 0)
     && <>(MAIN_MEMORY[0] == 1)
    )
}
#endif

/* A counterexample to this LTL formula proves that that there exists a trace
 * in which a cache line can eventually reach each of the MESI states. All
 * caches are symmetrical, it suffices to show this property for any one cache.
 */
ltl validate_cache_state {
    ! (
        <>(CACHES[0].lines[0].state == INVALID)
     && <>(CACHES[0].lines[0].state == SHARED)
     && <>(CACHES[0].lines[0].state == EXCLUSIVE)
     && <>(CACHES[0].lines[0].state == MODIFIED)
    )
}

#if MEMORY_SIZE > CACHE_SIZE
/* A counterexample to this LTL formula proves that that there exists a trace
 * in which a that tag of a cache line will eventually change. This property is
 * only true of configurations with MEMORY_SIZE > CACHE_SIZE. All caches are
 * symmetrical, it suffices to show this property for any one cache.
 */
ltl validate_cache_tag {
    ! (
        <>(CACHES[0].lines[0].tag == 0)
     && <>(CACHES[0].lines[0].tag != 0)
     )
}
#endif

/* A counterexample to this LTL formula proves that that there exists a trace
 * in which data in a cache line will eventually be altered. All caches are
 * symmetrical, it suffices to show this property for any one cache.
 */
#if !EXCLUDE_DATA_STORAGE
ltl validate_cache_data {
    ! (
        <>(CACHES[0].lines[0].data == 0)
     && <>(CACHES[0].lines[0].data == 1)
     )
}
#endif

/* A counterexample to these LTL formulas prove that that there exist a traces
 * in which each bus transaction will eventually occur.
 */
ltl validate_bus {
    ! (
        <>(BUS.op == NONE)
     && <>(BUS.op == BUS_RD)
     && <>(BUS.op == BUS_RDX)
     && <>(BUS.op == BUS_UPGR)
     && <>(BUS.op == FLUSH)
    )
}
#endif

/* Validate configuration parameters.
 */
#if NPROC < 2 || NPROC > 32
  #error Number of processors (NPROC) must be in range [2, 32].
#endif
#if CACHE_SIZE < 1
  #error CACHE_SIZE must be at least 1.
#endif
#if MEMORY_SIZE < 1 || MEMORY_SIZE > 64
  #error MEMORY_SIZE must be in range [1, 64].
#endif
#if MEMORY_SIZE < CACHE_SIZE
  #error MEMORY_SIZE should be greater than or equal to CACHE_SIZE.
#endif

