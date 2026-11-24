module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusCop

theorem natCoprime_of_zmod_mul_one_sub : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g →
    ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  intro I g T M hg hMg hz
  obtain ⟨t, ht, hc⟩ := hz
  obtain ⟨-, hint, hu, -⟩ := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I g hg
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set q : ℚ := (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) / (g : ℚ) with hqdef
  have hgq : (g : I.E) * (q : I.E) = (M : I.E) * (1 - (T : I.E)) := by
    have : (g : ℚ) * q = (M : ℚ) * (1 - (T : ℚ)) := by
      rw [hqdef]; field_simp; push_cast; ring
    have := congrArg (fun x : ℚ => (x : I.E)) this
    simpa using this
  have key : Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E) = t := by
    apply hu.mul_left_cancel
    rw [← hc]
    calc (g : I.E ⊗[I.F] Af I.F) * Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E)
        = Formalism.UG.inclE (F := I.F) (Af I.F) ((g : I.E) * (q : I.E)) := by rw [map_mul, map_natCast]
      _ = Formalism.UG.inclE (F := I.F) (Af I.F) ((M : I.E) * (1 - (T : I.E))) := by rw [hgq]
      _ = _ := by rw [map_mul, map_sub, map_one, map_natCast, map_natCast]
  have hq : (q : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := (hint _).1 (key ▸ ht)
  obtain ⟨b, hb⟩ := hq
  have h1 : IsIntegral ℤ (algebraMap ℚ I.E q) := by
    rw [eq_ratCast, ← hb]; exact RingOfIntegers.isIntegral_coe b
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : (M : ℤ) * (1 - (T : ℤ)) = (g : ℤ) * n := by
    have hn' : (n : ℚ) = q := by simpa using hn
    have : (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) = (((g : ℤ) * n : ℤ) : ℚ) := by
      rw [hqdef] at hn'
      push_cast
      rw [hn']
      field_simp
      push_cast; ring
    exact_mod_cast this
  have h5 : (g : ℤ) ∣ 1 - (T : ℤ) := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one ⟨n, h3⟩ ?_
    rw [Int.gcd_natCast_natCast]; exact hMg.symm
  have hd1 : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 := by
    have a : ((Nat.gcd T g : ℕ) : ℤ) ∣ (T : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have b : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 - (T : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans h5
    have := dvd_add b a
    simpa using this
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hd1))

end GlobalTheory.TorusCop
