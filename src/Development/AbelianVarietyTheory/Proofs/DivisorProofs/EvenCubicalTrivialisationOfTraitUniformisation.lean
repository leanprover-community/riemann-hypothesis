module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOnTorusDescendsAlongLocalHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem evenOn_of_unifTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  intro R _ _ _ _ D G _ _ P hG hU X _ _ _ hQ
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, -, hφ, hgp, hL, -⟩ := hU
  have hadm : AdmBase W (maximalIdeal W) := by
    haveI := hW.1
    exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap φ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)
  obtain ⟨P', hP', hE⟩ := unif_evenOn W hadm D' A' G' hG' U'
  have hpr : IsProper (pullback.snd G'.hom (jK W)) := by
    have := A'.isAb.proper
    haveI : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    change IsProper ((Over.pullback (jK W)).obj G').hom
    rw [← Over.w U'.gen.hom]
    infer_instance
  have hL' : LBIso P'.L.L (P.L.L.pull β) := by rw [hP']; exact hL
  exact GlobalTheory.T.evenOnTorus_descends_along_localHom R W φ hφ G hG G' β hgp hpr P P' hL' hE X hQ

end GlobalTheory.Mum
