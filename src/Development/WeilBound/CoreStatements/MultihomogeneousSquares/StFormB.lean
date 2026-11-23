module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

theorem stFormB : StForm := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ x 𝔐
  obtain ⟨hint, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J x 𝔐 RingOfIntegers.coe_injective
  have : IsLocallyNoetherian 𝔐.X := Cmp.HInterior.isLocallyNoetherian_of_coordTie 𝔐.ξ _ 𝔐.tie 𝔐.all
  let U : 𝔐.X.Opens :=
    ⟨abLocus 𝔐.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian 𝔐.t.G 𝔐.t.semi⟩
  have hU : genPt 𝔐.ξ ∈ U := hint
  obtain ⟨β, b, hb, hβ, hw⟩ := Cmp.HInterior.exists_homog_form_point 𝔐.ξ x 𝔐.tie U hU
  refine ⟨β, b, hb, hβ, fun z w hz hnot => ?_⟩
  by_contra hne
  have hmc : w ∈ mcPts (mCoordIdeal x) :=
    ⟨fun k => (hz.1 k).imp fun _ h => h.ne_zero, fun g hg => by
      rw [MvPolynomial.eval_map]
      exact ((tie_points _ _ 𝔐.ξ K J x 𝔐.tie ℂ).2.2 z _ (𝔐.all _) hz).1 g hg⟩
  obtain ⟨z', hz', hzU⟩ := hw w hmc hne
  have e : z = z' := GlobalTheory.T.normal_scheme_coords_injective _ _ 𝔐.ξ K J x 𝔐.tie 𝔐.normal 𝔐.all z z' w hz hz'
  subst e
  exact hnot hzU

end SquareStatements
