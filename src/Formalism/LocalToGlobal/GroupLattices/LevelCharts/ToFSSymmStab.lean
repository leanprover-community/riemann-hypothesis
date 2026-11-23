module

public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfCh
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmApply
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

structure StepG (I : LocId L p nV W Qq) (N : ℕ) where
  J : Matrix (Fin N) (Fin N) E
  hJ : IsHerm (sp.cm.sig : E →+* E) J
  hdet : IsUnit J.det
  Lb : Submodule (𝓞 E) (Fin N → E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))
  fr : FrS I Lb
  U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

variable {I : LocId L p nV W Qq} {N : ℕ}

def StepG.uGL (S : StepG I N) (v : Fin nV) :
    UPts sp.cm.sig S.J ((I.plc v).adicCompletion F) ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  locGL sp.cm.sig S.J S.hJ S.hdet _ (I.spl (I.plc v) (I.pl v).2) (I.spl_sig (I.plc v) (I.pl v).2)

def jPS (S : StepG I N) :
    (∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) →* UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F) :=
  (secAll F E sp.cm.sig S.J I.plc I.plc_inj).comp
    (MonoidHom.pi fun v => (S.uGL v).symm.toMonoidHom.comp (Pi.evalMonoidHom _ v))

abbrev frVS (S : StepG I N) (v : Fin nV) : GL (Fin N) ((I.plc v).adicCompletion F) := S.fr.fr (I.plc v) (I.pl v).2

def toFS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV) :
    GL (Fin (m + 1)) Qq ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  ((castGL hk Qq).trans (bcE (I.eQ v))).trans (MulAut.conj (frVS S v))

abbrev GAS (S : StepG I N) : Type := UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)

def jQS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) : (Fin nV → GL (Fin (m + 1)) Qq) →* GAS S :=
  (jPS S).comp (MonoidHom.pi fun v => (toFS S hk v).toMonoidHom.comp (Pi.evalMonoidHom _ v))

end Formalism.L2.G
