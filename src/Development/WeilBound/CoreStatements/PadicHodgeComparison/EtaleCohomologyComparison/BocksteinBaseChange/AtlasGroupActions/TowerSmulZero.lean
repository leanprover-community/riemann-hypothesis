module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CrystallineSemistableComparison.GlueE

theorem H_smul_eq_zero {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (r : R)
    (h : ∀ (T : C) (x : F.obj T), r • x = 0) (j : ℕ) (x : CH.H F j) : r • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul]
    have hz : r • z = 0 := Subtype.ext (funext fun s => h _ (z.1 s))
    rw [hz, Submodule.Quotient.mk_zero]

theorem padic_smul {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module A W]
    (f : ℤ_[l] →+* A) (n : ℕ) (w : W) (hw : ((l : A) ^ n) • w = 0) (z : ℤ_[l]) :
    f z • w = (PadicInt.toZModPow n z).val • w := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hmem : z - ((PadicInt.toZModPow n z).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  have hf : f z = f c * (l : A) ^ n + ((PadicInt.toZModPow n z).val : A) := by
    have : z = c * (l : ℤ_[l]) ^ n + ((PadicInt.toZModPow n z).val : ℤ_[l]) := by rw [hc]; ring
    conv_lhs => rw [this]
    rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast]
  rw [hf, add_smul, mul_smul, hw, smul_zero, zero_add, Nat.cast_smul_eq_nsmul]

theorem modF_smul {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) (r : R)
    (h : ∀ T, algebraMap R (A.obj T) r = 0) (T : C) (x : (CH.modF A).obj T) : r • x = 0 :=
  have hT : ∀ y : A.obj T, r • y = 0 := fun y => by rw [Algebra.smul_def, h, zero_mul]
  hT x

theorem tower_smul_zero {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : ℕ → (C ⥤ ModuleCat.{w} R))
    (r : ∀ n, F (n + 1) ⟶ F n) (j n : ℕ) (c : R) (h : ∀ (T : C) (x : (F n).obj T), c • x = 0) (x : (CH.towerH F r j).M n) :
    c • x = 0 :=
  H_smul_eq_zero (F n) c h j x

theorem lim_ext {R : Type} [CommRing R] {S : Sys.{w} R} {x y : S.lim} (h : ∀ n, x.1 n = y.1 n) : x = y :=
  Subtype.ext (funext h)

theorem lim_smul_val {R : Type} [CommRing R] (S : Sys.{w} R) (c : R) (x : S.lim) (n : ℕ) : (c • x).1 n = c • x.1 n := rfl

theorem lim_smul_fun {R : Type} [CommRing R] (S : Sys.{w} R) (c : R) (x : S.lim) : (c • x).1 = fun n => c • x.1 n := rfl

end CrystallineSemistableComparison.GlueE
