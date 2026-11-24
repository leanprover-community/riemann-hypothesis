module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem kaehler_rel_isInt (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω)
    (hS : ∀ x ∈ S, IsInt (p := p) x)
    (hι : ∀ x, ι x ∈ S) (D : Ω → Ω) (hD : GlobalTheory.KumDlog.IsDer S D) (a b c x y z : On p n)
    (hrel : a • KaehlerDifferential.D (O0 p) (On p n) x =
      b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z) :
    IsInt (p := p) (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  letI : Module (On p n) Ω := Module.compHom Ω ι.toRingHom
  have hsm : ∀ (r : On p n) (w : Ω), r • w = ι r * w := fun _ _ => rfl
  haveI : IsScalarTower (O0 p) (On p n) Ω := ⟨fun r s w => by
    rw [hsm, hsm, map_smul, smul_mul_assoc]⟩
  let N : Submodule (On p n) Ω :=
    { carrier := {w | IsInt (p := p) w}
      add_mem' := fun ha hb => int_add ha hb
      zero_mem' := int_zero
      smul_mem' := fun r w hw => by
        show IsInt (p := p) (r • w)
        rw [hsm]; exact int_mul (hS _ (hι r)) hw }
  have memN : ∀ w, w ∈ N ↔ IsInt (p := p) w := fun _ => Iff.rfl
  have key : ∀ w w' : Ω, IsInt (p := p) (w - w') → N.mkQ w = N.mkQ w' := fun w w' h =>
    (Submodule.Quotient.eq N).2 h
  let L : On p n →ₗ[O0 p] Ω ⧸ N :=
    { toFun := fun u => N.mkQ (D (ι u))
      map_add' := fun u v => by
        rw [← map_add (f := _)]
        refine key _ _ ?_
        rw [map_add (f := _)]
        exact int_congr (hD.1 _ (hι u) _ (hι v)) (by ring)
      map_smul' := fun r u => by
        simp only [RingHom.id_apply]
        rw [← LinearMap.map_smul_of_tower]
        refine key _ _ ?_
        rw [map_smul, Algebra.smul_def, Algebra.smul_def]
        exact hD.alg_mul hS r (hι u) }
  let d : Derivation (O0 p) (On p n) (Ω ⧸ N) := Derivation.mk' L (fun u v => by
    show N.mkQ (D (ι (u * v))) = u • N.mkQ (D (ι v)) + v • N.mkQ (D (ι u))
    rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add (f := _)]
    refine key _ _ ?_
    rw [hsm, hsm, map_mul]
    exact int_congr (hD.2.1 _ (hι u) _ (hι v)) (by ring))
  have hd : ∀ u, d.liftKaehlerDifferential (KaehlerDifferential.D (O0 p) (On p n) u) =
      N.mkQ (D (ι u)) := fun u => by
    rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
  have h2 := congrArg d.liftKaehlerDifferential hrel
  simp only [map_add (f := _), LinearMap.map_smul, hd] at h2
  rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add (f := _),
    ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, N.ker_mkQ, memN, hsm, hsm, hsm] at h2
  exact int_congr h2 (by ring)

end GlobalTheory.KumDlog
