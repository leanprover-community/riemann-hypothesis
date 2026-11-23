module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmLin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.harmNe :
    UpperTheory.V.Cj.HarmNe := by
  intro E _ _ _ a ha π Ξ r n e he hr hC
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have h0' : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | π.finPart k ⟨φ, hφ⟩ = ⟨φ, hφ⟩}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change π.finPart (x * y) _ = _
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        change π.finPart x⁻¹ _ = _
        conv_lhs => rw [← show π.finPart x ⟨φ, hφ⟩ = ⟨φ, hφ⟩ from hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hL : IsOpen (S : Set (GL (Fin a) (Af E))) := π.isSmooth_finPart _
  obtain ⟨K₀, ho₀, hc₀⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  have ho : IsOpen ((K₀ ⊓ S : Subgroup _) : Set (GL (Fin a) (Af E))) := ho₀.inter hL
  have hc : IsCompact ((K₀ ⊓ S : Subgroup _) : Set (GL (Fin a) (Af E))) :=
    hc₀.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
  obtain ⟨q, ω, w0, wH, wV⟩ := harmEx E a ha n e he _ hc π Ξ r hr hC ⟨⟨φ, hφ⟩, h0', fun k hk => hk.2⟩
  exact ⟨q, ω, w0, ⟨_, ho, hc, ((harmLin E a n e _ Ξ r q).2 ω).1 wH⟩, wH.closed, wH.coclosed, wV⟩
