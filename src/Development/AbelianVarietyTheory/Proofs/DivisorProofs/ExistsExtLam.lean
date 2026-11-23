module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvrStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumExt

theorem exists_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ L : LB ((Over.pullback (jK R)).obj G).left, L.IsLB → ∃ PP : LB (G2 G).left, ExtLam G L PP := by
  intro R _ _ _ G _ _ hG L hL
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected
  obtain ⟨L', hL', hb⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G L hL
  refine ⟨abelian₂ G L', DVR.linComb_isLB _ hL' _ _, fun κ₂ hκ => ?_⟩
  have h := isGrpPullback_pullback G (jK R)
  let V := lift (pushPt h.1.w (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
    (pushPt h.1.w (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
  have hV : V.left = κ₂ := by
    apply pullback.hom_ext
    · show (V ≫ fst G G).left = κ₂ ≫ (fst G G).left
      rw [hκ.1, lift_fst]
      rfl
    · show (V ≫ snd G G).left = κ₂ ≫ (snd G G).left
      rw [hκ.2, lift_snd]
      rfl
  have c := GlobalTheory.SymSpread.lbIso_cube h hL' hL hb (x2 G) (x2 _) V (fun i => by fin_cases i <;> simp [x2, V])
  rw [hV] at c
  exact c

end GlobalTheory.MumExt
