module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal

@[expose] public section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.link : UpperTheory.V.Z.Sym.Sig.Link := by
  intro k _ _ _ _ n
  have hTiw : (Lev.iw k).TH n = (glIwa k n).T := by
    apply le_antisymm (Lev.levelTorus_le_torus _)
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, fun i _ => ht i, rfl⟩
  have h2 : (Lev.iw k).J n = (glIwa k n).Iw 0 := by
    show (glIwa k n).N ⊔ (Lev.iw k).TH n ⊔ (glIwa k n).Nm 0 = (glIwa k n).N ⊔ (glIwa k n).T ⊔ (glIwa k n).Nm 0
    rw [hTiw]
  refine ⟨?_, h2, ?_⟩
  · obtain ⟨-, -, -, hU⟩ := memIwC k n ⊤
    have hK : Kc k n 1 = KOne k (Fin n) := by
      unfold Kc KOne
      congr 1
      ext g
      simp only [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.ext_iff, GeneralLinearGroup.map_apply,
        Units.val_one, Matrix.one_apply]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      have h1 : ∀ (I : Ideal 𝒪[k]) (x : 𝒪[k]), Ideal.Quotient.mk I x = 1 ↔ x - 1 ∈ I := fun I x => by
        rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
      have h0 : ∀ (I : Ideal 𝒪[k]) (x : 𝒪[k]), Ideal.Quotient.mk I x = 0 ↔ x ∈ I :=
        fun I x => Ideal.Quotient.eq_zero_iff_mem
      split_ifs
      · rw [h1]
        erw [h1]
        rw [pow_one]
      · rw [h0]
        erw [h0]
        rw [pow_one]
    have hTor : Subgroup.map (diagT k (Fin n)) (torC k n ⊤) = (Lev.iw k).TH n := by
      congr 1
      ext t
      simp only [torC, Subgroup.mem_pi, Set.mem_univ, true_implies]
      exact forall_congr' fun i => hU (t i)
    apply le_antisymm
    · show (glIwa k n).N ⊔ (Lev.iw k).TH n ⊔ (glIwa k n).Nm 0 ≤
        KOne k (Fin n) ⊔ unipO k n ⊔ Subgroup.map (diagT k (Fin n)) (torC k n ⊤)
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_sup_right.trans le_sup_left
      · rw [← hTor]
        exact le_sup_right
      · intro x hx
        have h1 : x ∈ Kc k n 1 := hx.2
        rw [hK] at h1
        exact (le_sup_left.trans le_sup_left :
          KOne k (Fin n) ≤ KOne k (Fin n) ⊔ unipO k n ⊔ Subgroup.map (diagT k (Fin n)) (torC k n ⊤)) h1
    · show KOne k (Fin n) ⊔ unipO k n ⊔ Subgroup.map (diagT k (Fin n)) (torC k n ⊤) ≤
        (glIwa k n).N ⊔ (Lev.iw k).TH n ⊔ (glIwa k n).Nm 0
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [← hK]
        exact kc_le (Lev.iw k)
      · exact (Lev.iw k).N_le
      · rw [hTor]
        exact le_sup_right.trans le_sup_left
  · intro c
    have hT : (Lev.deep k c).TH n = (glIwa k n).Tc c := by
      apply le_antisymm _ (Lev.Tc_le_TH _)
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨Lev.levelTorus_le_torus _ ⟨s, hs, rfl⟩, dg_mem_Kc.mpr fun i => hs i trivial⟩
    show (glIwa k n).N ⊔ (Lev.deep k c).TH n ⊔ (glIwa k n).Nm c =
      (glIwa k n).N ⊔ (glIwa k n).Tc c ⊔ (glIwa k n).Nm c
    rw [hT]

end
