module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaGeneratorEqRootOfUnityMul
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.theta_generator_eq_rootOfUnity_mul_alt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra ℚ S] (t' : SAB H (Sp S)) (x : Sp S ⟶ Xo.X) (m m' : SABMap t' Xo.univ.t x) (w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ)) (w' : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m'.φ)) (σ σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m.φ)) (s1' : LB.Sec (Xo.univ.t.PP.L.pull m'.φ)) (s : LB.Sec (PPx x)), SecGen x s → RigIso m w → RigIso m' w' → IsoMaps w σ s1 → IsoMaps w' σ' s1' → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m'.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m'.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1'.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → ∃ (ζ : S) (N : ℕ), 0 < N ∧ ζ ^ N = 1 ∧ ∀ i, σ'.f i = constFn t'.G.hom _ ζ * σ.f i := by
  first | exact @GlobalTheory.theta_generator_eq_rootOfUnity_mul | exact GlobalTheory.theta_generator_eq_rootOfUnity_mul | (intros; apply GlobalTheory.theta_generator_eq_rootOfUnity_mul <;> assumption)
