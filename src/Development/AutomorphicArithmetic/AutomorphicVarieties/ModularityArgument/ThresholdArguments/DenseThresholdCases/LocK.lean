module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.WeilDeligneFrobeniusEigenvalueOfFullFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWDAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.local_k_of_printed_rec_compat_sph_frob :
    _root_.UpperTheory.V.Af.Hypotheses' → RecTExists → CompatT → PlainRec → WinPt → RecSph → RecFrob → LocK := by
  intro P hRec hC hPR hW hSph hFrob K Ω _ _ _ _ _ _ l _ hl ι e he r π hc hreg hpol hatt w A κ hlw hA hex hplain
  obtain ⟨hfl, hI⟩ := hex
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hA _).2 hlw
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hκm : ∀ i (s : ↥(Dec (F := K) A)), (s : G K Ω) ∈ Ine (F := K) A →
      κ i s = cycBar K Ω l s ^ m i * (1 : G K Ω →* (Qbar l)ˣ) s := by
    intro i s hs
    fin_cases i
    · simpa [m] using (hI s hs).1
    · simpa [m] using (hI s hs).2
  have hor : ∀ i j, κ i ≠ κ j * (cycBar K Ω l).comp (Dec (F := K) A).subtype := by
    intro i j hij
    obtain ⟨s, hs, hne⟩ := UpperTheory.V.Ws.Pt.cycIne K Ω l A hAl (m i - m j - 1) (by
      fin_cases i <;> fin_cases j <;> simp [m] <;> omega)
    have h1 := congrArg (fun f => f ⟨s, Ine_le_Dec A hs⟩) hij
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    rw [hκm i _ hs, hκm j _ hs] at h1
    apply hne
    simp only [MonoidHom.one_apply, mul_one] at h1
    rw [zpow_sub, zpow_sub, h1, zpow_one]
    group
  have hfa : FlagAt 1 m r A κ := ⟨fun _ => 1, fun _ _ _ => rfl, hfl, hκm⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K 2 π w
  obtain ⟨rc, hrc⟩ := hRec K Ω A w hA
  obtain ⟨t, ht⟩ := hW K 2 (by norm_num) π
  obtain ⟨hpl, htor, hmono⟩ := hPR K Ω A w hA rc hrc 2 π t (ht w hplain) σ hσ
  have hgd : Gd (rc (algNorm σ)) := ⟨htor, hmono⟩
  obtain ⟨j, L0, hj0, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l K Ω w A hlw hA
  obtain ⟨Bw, hBj, -⟩ := hB L0 le_rfl
  have hj : Induces Bw := fun x => by rw [hBj]; exact hj0 x
  obtain ⟨HT, -, hcomp⟩ := hC K Ω l ι 2 (by norm_num) r π hc hreg hpol hatt
  obtain ⟨hpst, hwd⟩ := ((hcomp w σ hσ).1 A hA rc hrc).2 _ Bw hj hgd
  have hlev : IsLevelWD 1 2 (rc (algNorm σ)) := by
    rw [← hwd]
    exact _root_.UpperTheory.V.Af.weil_deligne_above_of_printed_results P K Ω l hl ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst (Or.inl hor)
  have hK : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := 2)) := hSph K Ω A w hA rc hrc 2 σ hpl hlev
  have hsat := _root_.UpperTheory.V.Af.satake_local_of_printed_results P K 2 w σ
  refine ⟨?_, fun B hBs τ hτ => ?_⟩
  · obtain ⟨B, hB'⟩ := hsat.1 hK
    exact ⟨B, (hsat.2 _ π.finPart (hiso σ hσ) B).2 hB'⟩
  · have hBσ := (hsat.2 _ π.finPart (hiso σ hσ) B).1 hBs
    let φ : ↥(Weil hA) := ⟨τ, mem_Weil_of_isFrob hA hτ⟩
    have hd : deg φ = 1 := deg_eq_one_iff.2 hτ
    have h1 := GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag K Ω l ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst 0 φ hd
    rw [hwd] at h1
    obtain ⟨b, hb, hzb⟩ := hFrob K Ω A w hA rc hrc 2 σ B hpl hBσ φ hd _ h1
    refine ⟨b, hb, ?_⟩
    exact hzb
end
end
