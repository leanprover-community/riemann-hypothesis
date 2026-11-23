module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_HuZ_v_dvd (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (k : ℕ) (z : ℤ_[PD.p]) (hz : (PD.p : ℤ_[PD.p]) ^ k ∣ z) :
    (k : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) := by
  obtain ⟨y, rfl⟩ := hz
  rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast, AddValuation.map_mul,
    AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (hv_int _)

theorem hv_holds (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) :=
  fun s z hz => Pf_HuZ_v_dvd W hv_int (s + 1) z hz

theorem huZ_holds (hu : ιZ uZ = (W.χΓ W.gam : O)) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)) := by
  intro k
  have : NeZero (PD.p ^ k) := ⟨pow_ne_zero _ (Fact.out : PD.p.Prime).ne_zero⟩
  have hdvd : (PD.p : ℤ_[PD.p]) ^ k ∣
      (uZ : ℤ_[PD.p]) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : ℤ_[PD.p]) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_self]
  have h := Pf_HuZ_v_dvd (ιZ := ιZ) W hv_int k _ hdvd
  rwa [map_sub, map_natCast, hu, map_sub, map_natCast] at h

end Formalism.MainNotions.N.Ln03.Pf
