module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def maxLam (i : X.Tw) (M : ℕ) (ι : Type) : Ideal (abelian₂ X i M ι) :=
  (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ⊔
    Ideal.span (Set.range fun q : ι => toLam X i M ι (MvPolynomial.X q))

theorem maxLam_ne_top (i : X.Tw) (M : ℕ) (ι : Type) : maxLam X i M ι ≠ ⊤ := by
  classical
  let ε : abelian₂ X i M ι →ₐ[X.O0 i] X.O0 i := MonoidAlgebra.lift (X.O0 i) (X.O0 i) (Del X i M ι) 1
  let φ : abelian₂ X i M ι →+* IsLocalRing.ResidueField (X.O0 i) :=
    (IsLocalRing.residue (X.O0 i)).comp ε.toRingHom
  have hle : maxLam X i M ι ≤ RingHom.ker φ := by
    unfold maxLam
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [φ, ε, IsLocalRing.residue_eq_zero_iff] using hc
    · rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      simp [φ, ε, toLam]
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top φ) hle

variable {X} (bkP : BKPh X)


end GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

end
