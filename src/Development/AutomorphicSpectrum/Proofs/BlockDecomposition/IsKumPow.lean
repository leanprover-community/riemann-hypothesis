module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KumPowProof

theorem isKum_pow {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v : (Γ(U, ⊤))ˣ) (k : ℕ) :
    ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ k * v → t U w = t U v + k • resGen 1 ζ := by
  induction k with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw, zero_smul, add_zero]
  | succ k ih =>
    intro w hw
    have hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v) := by rw [hw]; ring
    obtain ⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v) := isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)
    rw [ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]

theorem res_smap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun m => m.hom x) h).symm

theorem kumPow : LcCover → RepRoot → KapSpec → PrimAlg → KumPow := by
  intro hL _ hK _ hKum q _ U ζ f r v hr
  have ht : IsKum q (kumT q) := hKum q
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  obtain ⟨W, j, hf, -, -, hG⟩ := hL U (ZMod q) f
  obtain ⟨y, -, huniq⟩ := hG (ZMod q) ((res _ (tw q 1)).X 0) (fun a => Sec.res (j a) (kumT q U (r * v)))
  refine (huniq _ fun a => rfl).trans (huniq _ fun a => ?_).symm
  have hra : (j a).appTop.hom r.val = (primRes (j a) ζ).1 ^ a.val := hr (W a) (j a) a (hf a)
  have hlc : Sec.res (j a) (kap 1 ζ f) = (ULift.up a : ULift.{1} (ZMod q)) • twGen 1 (primRes (j a) ζ) :=
    (hK q 1 U ζ f).1 (W a) (j a) a (hf a)
  have hup : (ULift.up a : ULift.{1} (ZMod q)) = a.val • (1 : ULift.{1} (ZMod q)) :=
    ULift.ext (by change a = a.val • (1 : ZMod q); simp)
  have hsm : Sec.res (j a) (kap 1 ζ f) = a.val • twGen 1 (primRes (j a) ζ) := by
    rw [hlc, hup, smul_assoc, one_smul]
  have hkey := isKum_pow ht (primRes (j a) ζ) (Units.map (j a).appTop.hom.toMonoidHom v) a.val
    (Units.map (j a).appTop.hom.toMonoidHom (r * v)) (by
      change (j a).appTop.hom (r.val * v.val) = _ * (j a).appTop.hom v.val
      rw [map_mul, hra])
  have e1 : Sec.res (j a) (kumT q U (r * v)) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom (r * v)) :=
    ht.1 _ _ (j a) _ hq
  have e2 : Sec.res (j a) (kumT q U v) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom v) :=
    ht.1 _ _ (j a) _ hq
  have e3 : Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = a.val • resGen 1 (primRes (j a) ζ) := by
    rw [res_smap, hsm]
    exact map_nsmul _ _ _
  have e0 : Sec.res (j a) (kumT q U v + Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) =
      Sec.res (j a) (kumT q U v) + Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) := map_add _ _ _
  rw [e0, e1, e2, e3, hkey]

end GlobalTheory.CompanionTheory.KumPowProof
