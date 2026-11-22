module

public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.RT

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Polynomial CategoryTheory Formalism.MainNotions.PairedCharacterCondition

section Reps

open Formalism.IrreducibleCountingLemmas.TYPES (RepIso)

variable {Γ : Type} [Group Γ]

variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

end Reps

section Blocks

open Formalism.IrreducibleCountingLemmas.TYPES

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end Blocks

section Comparison₂

open Formalism.IrreducibleCountingLemmas.TYPES

end Comparison₂

section HC

open Formalism.IrreducibleCountingLemmas.TYPES

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} {O : LabelMap (ZMod g) C} {L : LzData g}

end HC

section Row

open Formalism.IrreducibleCountingLemmas.TYPES

variable {D : D7}

end Row

section Refute

open Formalism.IrreducibleCountingLemmas.TYPES

end Refute

section DZ

variable {D : D7}

def Occurs (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k)
    (z : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) : Prop :=
  ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F ≠ 0

def DZConcl (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i)
    (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ u : (ZMod (D.host.g k))ˣ, (u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹) ∧
    D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) ∧
    D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t ∧
    ∀ w', IsConjPl D.host (D.naut.plGw k v) w' →
      D.naut.mono0 (D.naut.locV i PI w') ∧
      (D.naut.items₂ k w' (D.naut.locV i PI w')).natDegree = D.R.nV ∧
      Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
        (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)

def AdmDepthZeroTypes : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (f : (ZMod (D.host.g k))[X]),
      Simple ρ → Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ →
      Occurs i PI k v (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) → Squarefree f →
      (∀ u : (ZMod (D.host.g k))ˣ, u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹ →
        ¬ f.IsRoot (u : ZMod (D.host.g k))) →
      DZConcl i k v PI f

def KtyTie (P : Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (τ : (P.lz k).Irr D.R.r),
    τ ∈ P.kty i PI k v → Occurs i PI k v ((P.lz k).idem τ)

theorem ktyTie_of_spec (P : Pend D) : KtyTie P := by
  intro i PI k v τ hτ
  exact (P.kty_spec i PI k v τ).1 hτ

theorem idem_mul_eSer (P : Pend D) (k : Fin 2) (τ : (P.lz k).Irr D.R.r) :
    (P.lz k).idem τ * D.ntypes.eSer k ((P.lz k).lab τ) = (P.lz k).idem τ := by
  rw [P.eSer_eq, Finset.mul_sum, Finset.sum_eq_single τ]
  · rw [if_pos rfl, (P.lz k).idem_idem τ]
  · intro σ _ hne
    split_ifs
    · exact (P.lz k).idem_orth τ σ (fun h => hne h.symm)
    · exact mul_zero _
  · intro h
    exact absurd (Finset.mem_univ τ) h

end DZ

section TY

open Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end TY

end Formalism.MainNotions.PairedCharacterCondition.RT

end
