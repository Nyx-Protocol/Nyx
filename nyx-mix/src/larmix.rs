//! Loopix-inspired mix node selection using exponential distributions
//! Low-latency anonymous routing with mix network design.

use rand::Rng;
use rand_distr::{Distribution, Exp};

#[derive(Debug, Clone)]
pub struct Candidate {
    pub id: String,
    pub rtt_ms: u32,
}

impl Candidate {
    pub fn new(id: String, rtt_ms: u32) -> Self {
        Self { id, rtt_ms }
    }
}

/// Select mix node using exponential distribution (Loopix-style)
/// Lower RTT nodes have higher probability of selection
///
/// # Performance Optimizations
/// - Single-pass enumeration with fold to avoid intermediate Vec allocation
/// - Inline computation of weights during iteration
/// - Minimal memory footprint for high-frequency path selection
#[inline]
pub fn select_mix_node<'a>(
    candidates: &'a [Candidate],
    rng: &'a mut impl Rng,
) -> Option<&'a Candidate> {
    if candidates.is_empty() {
        return None;
    }

    // Single-pass optimization: find max weight during iteration without intermediate Vec
    // Use fold to track (index, max_weight) in one pass
    let (max_idx, _) =
        candidates
            .iter()
            .enumerate()
            .fold((0, f64::NEG_INFINITY), |(max_i, max_w), (i, c)| {
                // Compute weight inline without Vec allocation
                let rate = 1.0 / (c.rtt_ms as f64 + 1.0);
                let weight = Exp::new(rate)
                    .unwrap_or_else(|_| Exp::new(1.0).unwrap())
                    .sample(rng);

                if weight > max_w {
                    (i, weight)
                } else {
                    (max_i, max_w)
                }
            });

    candidates.get(max_idx)
}

/// Build multi-hop path through mix network
///
/// # Performance Optimizations
/// - Pre-allocate result Vec with exact capacity
/// - Minimize String clones with single clone and retain
/// - Use Vec indices to avoid full Vec clone per iteration
#[inline]
pub fn build_mix_path(candidates: &[Candidate], hops: usize, rng: &mut impl Rng) -> Vec<String> {
    // Pre-allocate with exact capacity to avoid reallocation
    let mut path = Vec::with_capacity(hops);
    let mut remaining: Vec<Candidate> = candidates.to_vec();

    for _ in 0..hops {
        if let Some(selected) = select_mix_node(&remaining, rng) {
            // Single clone of selected_id
            let selected_id = selected.id.clone();
            path.push(selected_id.clone());
            // Remove selected node to avoid loops - retain is efficient for small Vec
            remaining.retain(|c| c.id != selected_id);
        } else {
            break;
        }
    }

    path
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;

    #[test]
    fn test_select_mix_node() {
        let candidates = vec![
            Candidate::new("fast".to_string(), 10),
            Candidate::new("slow".to_string(), 100),
            Candidate::new("medium".to_string(), 50),
        ];

        let mut rng = thread_rng();
        let selected = select_mix_node(&candidates, &mut rng);
        assert!(selected.is_some());
        assert!(candidates.iter().any(|c| c.id == selected.unwrap().id));
    }

    #[test]
    fn test_empty_candidates() {
        let candidates = vec![];
        let mut rng = thread_rng();
        assert!(select_mix_node(&candidates, &mut rng).is_none());
    }

    #[test]
    fn test_build_mix_path() {
        let candidates = vec![
            Candidate::new("node1".to_string(), 20),
            Candidate::new("node2".to_string(), 30),
            Candidate::new("node3".to_string(), 40),
            Candidate::new("node4".to_string(), 50),
        ];

        let mut rng = thread_rng();
        let path = build_mix_path(&candidates, 3, &mut rng);

        assert!(path.len() <= 3);
        assert!(path.len() <= candidates.len());

        // Ensure no duplicates in path
        let mut unique_path = path.clone();
        unique_path.sort();
        unique_path.dedup();
        assert_eq!(path.len(), unique_path.len());
    }

    #[test]
    fn test_path_longer_than_candidates() {
        let candidates = vec![Candidate::new("only".to_string(), 20)];

        let mut rng = thread_rng();
        let path = build_mix_path(&candidates, 5, &mut rng);
        assert_eq!(path.len(), 1); // Can't build path longer than available nodes
    }
}
