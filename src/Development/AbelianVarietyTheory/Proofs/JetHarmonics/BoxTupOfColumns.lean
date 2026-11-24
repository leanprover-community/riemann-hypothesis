module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermBoxProductEqProdGermsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqOneOfMultilinear
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdPullZero
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxMaps
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpBijFOfAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LinOfSval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem boxTup_of_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ Q hQ F _ _ _ _ v g g' π hg hg' hπ τ hτ hEL n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
    s s₂ t₀ t p w ζ x σ f h
  have hG := hL.globalFns
  have hk : 1 ≤ g' * g := Nat.mul_pos hg' hg
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F g'
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (g' * g)
  obtain ⟨p', hp'⟩ := BoxQk.exists_isBoxQk hG T.V n P.D.toPre D'.toPre pD F (g' * g) p
  have hw : ∀ i, (w i).IsGen := fun i => (h i).2.2.1
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (g' * g) p' p hp' w hw
  obtain ⟨σ', hσ', -⟩ := (expandsG_bijective_of_dvr hL hL2 hL4 hT T.V D' A' G' U' F (g' * g) hk).2 (bx t)
  let x' : TFK (R := T.V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ x)
  have hx' : ∀ i, x' ≫ pA.pr i = x i := fun i => pA.lim.fac (Fan.mk _ x) ⟨i⟩
  have hπ' : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm, hπ]
  refine ⟨bx₁ s, bx s₂, p', w', ∏ i, ζ i, x', bx t₀, bx t, σ', ⟨?_, ?_, ⟨hw', ?_, ?_⟩, ?_, ?_, ?_, ?_, hσ', ?_⟩, hx'⟩
  · have := NuBox.main T.V ϖ hϖ n P.D D' pD Q hQ F v g' s (bx₁ s) ((hbx₁ _ _).2 rfl) (fun _ => 0) (fun i => (h i).1)
    rw [Finset.sum_const_zero] at this
    exact this
  · exact BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact (star π) g g' hg hg' hπ' s s₂ _ _
      (fun i => (h i).2.1) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  · exact Finset.prod_ne_zero_iff.2 fun i _ => (h i).2.2.2.1
  · exact finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (g' * g) hk p' p hp' w w' hw hw' hΦ ζ (fun i => (h i).2.2.2.2.1)
  · exact ProdTorsion.qkToAk_box hL T.V _ n P.D D' P.A A' C.I.G.G G' pD pA pG U' P.U PU
      (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ P.U) (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ U') F (g' * g) hk
      p' p hp' x' x hx' (fun i => (h i).2.2.2.2.2.1)
  · intro i
    rw [← Category.assoc, hx']
    exact (h i).2.2.2.2.2.2.1
  · exact hΦ s₂ t₀ _ _ (fun i => (h i).2.2.2.2.2.2.2.1) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl)
  · refine (isSmul_iff _ _ _).2 ?_
    calc
      bx t = bx (fun i => ζ i • t₀ i) :=
        congrArg bx (funext fun i => (isSmul_iff _ _ _).1 (h i).2.2.2.2.2.2.2.2.1)
      _ = (∏ i, ζ i) • bx t₀ := by simpa using bx.map_smul_univ ζ t₀
  · exact GlobalTheory.T.germ_boxProduct_eq_prod_germs hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
      C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (g' * g) hk σ t f σ' (bx t)
      (fun i => (h i).2.2.2.2.2.2.2.2.2) ((hbx _ _).2 rfl) hσ'

end GlobalTheory
