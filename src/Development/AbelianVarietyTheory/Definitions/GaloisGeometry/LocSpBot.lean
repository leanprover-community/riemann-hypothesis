module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
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

@[expose] public section

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

def locSp {E : Type} [Field E] [NumberField E] (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] (ρ : E →+* K) {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) : Submodule R (Fin N → K) :=
  Submodule.span R ((fun (x : Fin N → E) k => ρ (x k)) '' (L : Set (Fin N → E)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def SplAlg (A : LocAt F E n G) : Prop :=
  ∀ v (x : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] x) = (x, x)

def LbAtB (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v : Fin G.P.nV, locSp (G.P.W v) (A.iw v) Lb =
    colSpan (G.P.W v) ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))

def facQ (A : LocAt F E n G) (v : Fin G.P.nV) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (G.P.Qq v) :=
  bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) y))

def LatAdLoc (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : Fin G.P.nV),
    locSp (G.P.W v) (A.iw v) (Formalism.L2.PairingIndexBounds.F.latAd y Lb) =
      (locSp (G.P.W v) (A.iw v) Lb).map (((facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)).mulVecLin).restrictScalars (G.P.W v))

end GlobalTheory.TwV

end
