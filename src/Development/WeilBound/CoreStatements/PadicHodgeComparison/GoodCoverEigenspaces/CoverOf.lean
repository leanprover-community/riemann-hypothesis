module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.LocalHodgeTateComplexTower
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateSpectral.HTSpecGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

variable {l : ℕ} [Fact l.Prime]

def GoodModel {K : FinExt l} {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (M : CrystallineSemistableComparison.Model l K.1) : Prop :=
  M.Sm ∧ (∃ d, SmoothOfRelativeDimension d M.p) ∧ ∃ e : M.gen ≅ X, e.hom ≫ q = M.q

def HasGoodCovers {K : FinExt l} (H : HTower ↥K.1) {J : Type} (ι : J → H.Γ) : Prop :=
  ∃ (MZ : CrystallineSemistableComparison.Model l K.1) (eZ : MZ.gen ≅ H.Z), GoodModel H.q MZ ∧ eZ.hom ≫ H.q = MZ.q ∧ ∀ j, ∃ (W : Scheme.{0})
    (c : W ⟶ H.Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (I : Type) (_ : Fintype I) (σ : I → (W ⟶ H.Y (ι j))),
    IsGalois c G a ∧ Splits (H.s (ι j)) c σ ∧ ∃ (MW : CrystallineSemistableComparison.Model l K.1) (eW : MW.gen ≅ W), GoodModel (c ≫ H.q) MW ∧
      (∃ (uc : MW.X ⟶ MZ.X) (hu : uc ≫ MZ.p = MW.p), CrystallineSemistableComparison.Model.genMap uc hu ≫ eZ.hom = eW.hom ≫ c) ∧
      ∀ i, ∃ (ui : MW.X ⟶ MZ.X) (hu : ui ≫ MZ.p = MW.p), CrystallineSemistableComparison.Model.genMap ui hu ≫ eZ.hom = eW.hom ≫ σ i ≫ H.t (ι j)

def CoverOf : Prop :=
  CrystallineSemistableComparison.HTSpecB.HTSpecGood → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : HTower ↥K.1) {J : Type} (ι : J → H.Γ),
    HasGoodCovers H ι → ∀ n, HTCover H ι n

end PositivityTheory.AutomorphicGaloisHodgeTate.G8
