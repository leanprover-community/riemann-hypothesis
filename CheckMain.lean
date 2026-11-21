import Main
import Lean.Elab.Command
import Lean.Util.CollectAxioms

namespace ChallengeSpecification
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
end ChallengeSpecification


private def guardPublicTheoremAxioms (name : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  unless (← Lean.getEnv).contains name do
    throwError "Missing declaration {name}"
  let permitted : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let used ← Lean.collectAxioms name
  let extra := used.filter fun axiomName => !(permitted.contains axiomName)
  unless extra.isEmpty do
    throwError "{name} depends on unapproved axioms {extra}"

example : RiemannHypothesis := riemannHypothesis

run_cmd guardPublicTheoremAxioms `riemannHypothesis

#print axioms riemannHypothesis

example : ChallengeSpecification.RiemannZetaZerosOnLine := riemannZeta_eq_zero_re

run_cmd guardPublicTheoremAxioms `riemannZeta_eq_zero_re

#print axioms riemannZeta_eq_zero_re

example : ChallengeSpecification.DirichletLNonvanishingRightOfHalf := LFunction_ne_zero_of_half_lt_re

run_cmd guardPublicTheoremAxioms `LFunction_ne_zero_of_half_lt_re

#print axioms LFunction_ne_zero_of_half_lt_re

example : ChallengeSpecification.DirichletLZerosOnLine := LFunction_eq_zero_re

run_cmd guardPublicTheoremAxioms `LFunction_eq_zero_re

#print axioms LFunction_eq_zero_re

example : ChallengeSpecification.PrimitiveDirichletLZerosOnLine := LFunction_eq_zero_re_of_isPrimitive

run_cmd guardPublicTheoremAxioms `LFunction_eq_zero_re_of_isPrimitive

#print axioms LFunction_eq_zero_re_of_isPrimitive
