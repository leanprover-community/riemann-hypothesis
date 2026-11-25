module

public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

open scoped TensorProduct

namespace GlobalTheory.LocCarry

theorem prV_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (fun i => prV (E := E) v ((M *ᵥ w) i)) = M.map (prV (E := E) v) *ᵥ (fun i => prV (E := E) v (w i)) := by
  ext i

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem coe_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := by
  rw [← map_inv]
  rfl

theorem coe_bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ((bc (prV (E := E) v) x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      (x : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := rfl

theorem mem_latS_latAd_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x Lb) ↔
        (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb := by
  intro F E _ _ _ _ _ _ N x Lb hfin hspan v z
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x
  have hpr : ∀ y : Fin N → E ⊗[F] v.adicCompletion F,
      (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE v (y i))) = y := fun y => by
    ext i; exact Formalism.UG.P.afsplit_prV_IE v (y i)
  have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  constructor
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS (Formalism.UG.CS.globLat x Lb) v hz
    have h2 := (hrec _).1 h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS Lb v h2
    rw [prV_mulVec, hpr, ← coe_bc_inv] at h3
    exact h3
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS Lb v hz
    set u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
      ((x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
        (fun i => Formalism.UG.P.afsplitIE v (((((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z) i)) with hu
    have h2 : u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.UG.CS.globLat x Lb) := by
      refine (hrec u).2 ?_
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS (Formalism.UG.CS.globLat x Lb) v h2
    rw [hu, prV_mulVec, hpr, ← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.LocCarry
