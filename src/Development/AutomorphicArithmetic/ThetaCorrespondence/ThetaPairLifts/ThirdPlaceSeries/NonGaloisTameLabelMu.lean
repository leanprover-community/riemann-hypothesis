module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacterStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGwStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiUnrAtStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.PendOf.tame_label_mu_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ChiTOk D P.cf → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  intro hP hL D P hchi S hS i k v hw
  obtain ⟨u, hu0, hunit, hrep⟩ := GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character D k v
  have hrep' : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u := by
    obtain ⟨ϖ, π, h1, h2, h3, h4⟩ := hrep
    exact ⟨D.nd.plOm.1 (D.naut.plGw k v), D.nd.plOm.2 (D.naut.plGw k v), D.ntypes.tg_mem k v, ϖ, π, h1, h2, h3,
      by rw [zpow_one]; exact h4⟩
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  obtain ⟨c, hc, hcv⟩ := hchi k v j u hu0 hrep'
  have htame := _root_.GlobalTheory.T.split_weil_mu_tame_of_is_true hL D P S hS i k v hw
  refine ⟨htame, (S i _ hw).mu_ok.1, c, hc, _root_.UpperTheory.Lit.Dz.dz_swap_compatible_alt hL D P.ty.grp k v _ _ htame u hu0 hrep c ?_⟩
  rw [_root_.GlobalTheory.T.split_mu_unit_eq_mu0_loc_k hL D P S hS i k v hw j (by simp only [j]; omega) u hu0 hunit]
  exact hcv.symm
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ChiTOk D P.cf → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  exact @_root_.GlobalTheory.PendOf.tame_label_mu_alt
end
end
