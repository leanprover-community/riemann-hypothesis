module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataTies

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def lvlForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (r : Representation K G S.Forms)
    (P : Subgroup G) (ψ : P →* Kˣ) : Set S.Forms := {f | ∀ h : P, r (h : G) f = ((ψ h : Kˣ) : K) • f}

def intForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) : Set S.Forms :=
  {f | ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c}

section Basic

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (r : Representation K G S.Forms)

end Basic

namespace SideTie

variable {R : RealDat D A Ks} {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
  [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (Y : SideTie R F tup b S)

end SideTie

section Fibre

variable {V H I J : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup H] [Module ℂ H]

end Fibre

namespace RowsTieSum

variable {R : RealDat D A Ks} {F : Face D A} {X0 : BaseLevelRowSide D} (Y : RowsTieSum R F X0)

end RowsTieSum

namespace RowsTie

variable {R : RealDat D A Ks} {F : Face D A} {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0)

end RowsTie

end GlobalTheory.Mem

end
