module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowDim

theorem smoothOfRelativeDimension_of_eighthPower : ∀ {S : Scheme.{0}} [IsIntegral S] (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) (hG : IsSemiAbelian G) (hH : SmoothOfRelativeDimension (8 * g) H.hom), SmoothOfRelativeDimension g G.hom := by
  intro S _ G H _ _ g pr huniv hG hH
  have hlim : IsLimit (Fan.mk H pr) :=
    mkFanLimit _ (fun s => (huniv s.pt s.proj).choose) (fun s i => (huniv s.pt s.proj).choose_spec.1 i)
      (fun s m hm => (huniv s.pt s.proj).choose_spec.2 m hm)
  let e : H ≅ powObj G 8 := hlim.conePointUniqueUpToIso (powIsLimit G 8)
  have hw : H.hom = e.hom.left ≫ (powObj G 8).hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : ConnectedSpace S := inferInstance
  haveI : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨s⟩ : Nonempty S := inferInstance
  obtain ⟨n, hn⟩ := Geo.Tor.exists_dim_of_preconnected G.hom (eSec G s)
  have h8 := smoothOfRelativeDimension_powObj G n hn 8
  have h2 : SmoothOfRelativeDimension (0 + 8 * n) H.hom := by
    rw [hw]; infer_instance
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ hH h2 (eSec H s)
  have hgn : g = n := by omega
  subst hgn
  exact hn

end GlobalTheory.PowDim
