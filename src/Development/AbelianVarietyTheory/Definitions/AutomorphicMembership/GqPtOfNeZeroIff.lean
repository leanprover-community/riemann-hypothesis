module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PrimInIffSubsingleton
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P



variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

variable (t : Term σ J T' g P)

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}






namespace Term

variable (t : Term σ J T' g P)

variable {t}

variable (t)

end Term

end Basic

section Examples

variable {E : Type} [Field E] [NumberField E]

end Examples

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coMat (V : HSpace E) {a : Type} (x : a → V.V) : Matrix (Fin V.rank) a E :=
  Matrix.of fun i b => V.frame.repr (x b) i

theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

end Spaces

section Record


attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

variable {D} {u u' : D.what₂.Word}

end Record

end GlobalTheory.IntTerm
