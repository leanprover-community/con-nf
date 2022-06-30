import tactic.alias
import tactic.protected

alias heq_iff_eq ↔ heq.eq eq.heq

attribute [protected] heq.eq eq.heq
