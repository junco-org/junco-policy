#![cfg(verus_keep_ghost)]

mod spec {
    mod hypotheses {
        use history_syntax::Component3;
        use junco_core::spec::hypotheses::{
            analyzer_hypotheses, hash_coherent, lemma_u8_event_hypotheses,
            lemma_u32_event_hypotheses, monitor_hypotheses,
        };
        use vstd::prelude::*;

        verus! {

        /// A public client discharges every event/equality premise, leaving container faithfulness.
        proof fn u8_hypothesis_smoke()
            requires hash_coherent::<Component3<u8, u8, u8>>(),
            ensures monitor_hypotheses::<(u8, u8, u8)>(), analyzer_hypotheses::<(u8, u8, u8)>(),
        {
            lemma_u8_event_hypotheses();
        }

        /// The same public contract also covers an event with a wider coordinate.
        proof fn u32_hypothesis_smoke()
            requires hash_coherent::<Component3<u32, u8, u8>>(),
            ensures monitor_hypotheses::<(u32, u8, u8)>(), analyzer_hypotheses::<(u32, u8, u8)>(),
        {
            lemma_u32_event_hypotheses();
        }

        }
    }
}
