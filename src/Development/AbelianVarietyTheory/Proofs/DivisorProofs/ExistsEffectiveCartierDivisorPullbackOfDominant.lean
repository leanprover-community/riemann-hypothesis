module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.Cartier.PullDominant

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]

theorem unitAt_map {x : M} {u : W.functionField} (h : UnitAt (f x) u) :
    UnitAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨f.stalkMap x a, ha.map _, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

theorem regAt_map {x : M} {u : W.functionField} (h : RegAt (f x) u) :
    RegAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

abbrev unitsMap : W.functionFieldˣ →* M.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap f).toMonoidHom

theorem germOf_map_eq {D₀ : CartierDiv W} {x : M} {g g' : W.functionFieldˣ}
    (h : D₀.IsEqn (f x) g) (h' : D₀.IsEqn (f x) g') :
    germOf x (unitsMap f g) = germOf x (unitsMap f g') := by
  rw [germOf_eq_iff]
  have := unitAt_map f (h.iff_unitAt.1 h')
  simpa [map_div₀] using this

def pullGerm (D₀ : CartierDiv W) (x : M) : Germ x :=
  germOf x (unitsMap f (D₀.exists_isEqn (f x)).choose)

theorem pullGerm_eq {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    pullGerm f D₀ x = germOf x (unitsMap f g) :=
  germOf_map_eq f (D₀.exists_isEqn (f x)).choose_spec h

def pull (D₀ : CartierDiv W) : CartierDiv M :=
  show cartierGroup M from ⟨pullGerm f D₀, fun x => by
    obtain ⟨U, hU, g, hg⟩ := D₀.exists_isEqn_nhds (f x)
    exact ⟨f ⁻¹ᵁ U, hU, unitsMap f g, fun y hy => pullGerm_eq f (hg (f y) hy)⟩⟩

theorem isEqn_pull {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    (pull f D₀).IsEqn x (unitsMap f g) :=
  pullGerm_eq f h

theorem eff_pull {D₀ : CartierDiv W} (hD : D₀.Eff) : (pull f D₀).Eff := by
  intro x
  obtain ⟨g, hg⟩ := D₀.exists_isEqn (f x)
  refine ⟨unitsMap f g, isEqn_pull f hg, ?_⟩
  rw [one_mul]
  exact regAt_map f (CartierDiv.eff_iff.1 hD _ _ hg)

end GlobalTheory.Cartier.PullDominant


open GlobalTheory.Cartier.PullDominant in
theorem GlobalTheory.Cartier.exists_pull_dominant :
    ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W), D₀.Eff → ∃ D₁ : CartierDiv M, D₁.Eff ∧ ∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g) := by
  intro M W _ _ f _ D₀ hD
  exact ⟨pull f D₀, eff_pull f hD, fun x g h => isEqn_pull f h⟩
