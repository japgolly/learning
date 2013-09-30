// convert 


trait λ {
  type eval<:λ
  type ap[_<:λ]<:λ
}

def Eq[A<:λ, B<:λ](implicit ev: A#eval =:= B#eval) = true

trait λFinn extends λ {
   type ap[n<:λ] = eval#ap[n]
}

trait ~[x<:λ,y<:λ] extends λ {
  type self = x#ap[y]
  type ap[z<:λ] = self#ap[z]
  type eval = self#eval
}

trait Ap2 extends λ { type ap2[x<:λ,y<:λ] = ap[x]#ap[y] }
trait Ap3 extends Ap2 { type ap3[x<:λ,y<:λ,z<:λ] = ap[x]#ap[y]#ap[z] }

trait λF1 { type ap[x<:λ]<:λ }
trait λ1_1[F<:λF1, x<:λ] extends λFinn { type eval = F#ap[x]#eval }
trait λ1[F<:λF1] extends λ{
  type eval = λ1[F]
  type ap[x<:λ] = λ1_1[F,x]
}

trait λF2 { type ap[x<:λ, y<:λ]<:λ }
trait λ2_2[F<:λF2, x<:λ, y<:λ] extends λFinn { type eval = F#ap[x,y]#eval }
trait λ2_1[F<:λF2, x<:λ] extends λ{
  type eval = λ2_1[F,x]
  type ap[y<:λ] = λ2_2[F,x,y]
}
trait λ2[F<:λF2] extends Ap2{
  type eval = λ2[F]
  type ap[x<:λ] = λ2_1[F,x]
}

trait λF3 { type ap[x<:λ, y<:λ, z<:λ]<:λ }
trait λ3_3[F<:λF3, x<:λ, y<:λ, z<:λ] extends λFinn { type eval = F#ap[x,y,z]#eval }
trait λ3_2[F<:λF3, x<:λ, y<:λ] extends λ{
  type eval = λ3_2[F,x,y]
  type ap[z<:λ] = λ3_3[F,x,y,z]
}
trait λ3_1[F<:λF3, x<:λ] extends Ap2{
  type eval = λ3_1[F,x]
  type ap[y<:λ] = λ3_2[F,x,y]
}
trait λ3[F<:λF3] extends Ap3{
  type eval = λ3[F]
  type ap[x<:λ] = λ3_1[F,x]
}

type I = λ1[λF1 { type ap[x<:λ] = x }]
type K = λ2[λF2 { type ap[x<:λ,y<:λ] = x }]
type S = λ3[λF3 { type ap[x<:λ,y<:λ,z<:λ] = x#ap[z]#ap[y#ap[z]] }]
/*
trait I_ extends λF1 { type ap[x<:λ] = x }
trait I extends λ1[I_]

trait K_ extends λF2 { type ap[x<:λ,y<:λ] = x }
trait K extends λ2[K_]

trait S_ extends λF3 { type ap[x<:λ,y<:λ,z<:λ] = x#ap[z]#ap[y#ap[z]] }
trait S extends λ3[S_]
*/

type I2 = S#ap2[K,K]

trait α extends λ {type eval = α}
trait ∅ extends λ {type eval = ∅}
trait d1 extends λ {type eval = d1}
trait d2 extends λ {type eval = d2}
trait d3 extends λ {type eval = d3}
Eq[d1, I#ap[d1]]
Eq[d1, K#ap[d1]#ap[d2]]
Eq[d1, S#ap[K]#ap[K]#ap[d1]]
Eq[d1, I2#ap[d1]]


type T = λ2[λF2 { type ap[x<:λ,y<:λ] = x }]
type F = λ2[λF2 { type ap[x<:λ,y<:λ] = y }]

type And = λ2[λF2 { type ap[x<:λ,y<:λ] = x#ap[y]#ap[x] }]
Eq[T, And#ap[T]#ap[T]]
Eq[F, And#ap[T]#ap[F]]
Eq[F, And#ap[F]#ap[T]]
Eq[F, And#ap[F]#ap[F]]

type Or = λ2[λF2 { type ap[x<:λ,y<:λ] = x#ap[x]#ap[y] }]
Eq[T, Or#ap[T]#ap[T]]
Eq[T, Or#ap[T]#ap[F]]
Eq[T, Or#ap[F]#ap[T]]
Eq[F, Or#ap[F]#ap[F]]
Eq[T, Or#ap2[T,T]]
Eq[T, Or#ap2[T,F]]
Eq[T, Or#ap2[F,T]]
Eq[F, Or#ap2[F,F]]

type If = λ3[λF3 { type ap[m<:λ,a<:λ,b<:λ] = m#ap[a]#ap[b] }]
Eq[d1, If#ap[T]#ap[d1]#ap[d2]]
Eq[d2, If#ap[F]#ap[d1]#ap[d2]]
Eq[d1, If#ap3[T,d1,d2]]
Eq[d2, If#ap3[F,d1,d2]]
Eq[d1, If#ap[T]#ap2[d1,d2]]
Eq[d2, If#ap[F]#ap2[d1,d2]]

Eq[d1, If ~ T ~ d1 ~ d2]
Eq[d2, If ~ F ~ d1 ~ d2]

// Pairs
type Ky = λ2[λF2 { type ap[x<:λ,y<:λ] = y }]
type pair = λ3[λF3 { type ap[x<:λ,y<:λ,z<:λ] = z ~ x ~ y }]
type fst = λ1[λF1 { type ap[x<:λ] = x ~ K }]
type snd = λ1[λF1 { type ap[x<:λ] = x ~ Ky }]
Eq[d1, fst ~ (pair ~ d1 ~ d2)]
Eq[d2, snd ~ (pair ~ d1 ~ d2)]

type NIL = pair ~ T ~ T
type ISNIL = fst
type CONS = λ2[λF2 { type ap[h<:λ,t<:λ] = pair ~ F ~ (pair ~ h ~ t) }]
type HEAD = λ1[λF1 { type ap[z<:λ] = fst ~ (snd ~ z) }]
type TAIL = λ1[λF1 { type ap[z<:λ] = snd ~ (snd ~ z) }]

type L_d1 = CONS ~ d1 ~ NIL
type L_d21 = CONS ~ d2 ~ L_d1
// type L_d21 = CONS ~ d2 ~ (CONS ~ d1 ~ NIL)
Eq[T, ISNIL ~ NIL]
Eq[F, ISNIL ~ L_d1]
Eq[d1, HEAD ~ L_d1]
Eq[L_d1, TAIL ~ L_d21]
Eq[NIL, TAIL ~ L_d1]
Eq[T, ISNIL ~ (TAIL ~ L_d1)]


type Yx[f<:λ] = λ1[λF1 { type ap[x<:λ] = f ~ (x ~ x) }] 
type Y = λ1[λF1 { type ap[f<:λ] = Yx[f] ~ Yx[f] }]

/*
def contains(X, list) = list match {
  case Nil => false
  case h :: t => h == X || contains(X, t)
}
*/

type CONTAINS_[x<:λ] = λ2[λF2 {
  type ap[f<:λ,l<:λ] = If ~ (ISNIL ~ l) ~ F ~ cmpHT[f,HEAD ~ l,TAIL ~ l]
  type cmpHT[f<:λ,h<:λ,t<:λ] = Or ~ cmpH[h] ~ (f ~ t)
  type cmpH[h<:λ] = h
  }]
type CONTAINS = λ2[λF2 { type ap[x<:λ,l<:λ] = (Y ~ CONTAINS_[x]) ~ l }]

type TFF = CONS ~ T ~ (CONS ~ F ~ (CONS ~ F ~ NIL))
type FTF = CONS ~ F ~ (CONS ~ T ~ (CONS ~ F ~ NIL))
type FFT = CONS ~ F ~ (CONS ~ F ~ (CONS ~ T ~ NIL))
type FFF = CONS ~ F ~ (CONS ~ F ~ (CONS ~ F ~ NIL))
Eq[F, CONTAINS ~ T ~ FFF]
Eq[T, CONTAINS ~ T ~ FFT]
Eq[T, CONTAINS ~ T ~ FTF]
Eq[T, CONTAINS ~ T ~ TFF]

type N0 = λ2[λF2 { type ap[f<:λ,x<:λ] = x }]
type N1 = λ2[λF2 { type ap[f<:λ,x<:λ] = f ~ x }]
type N2 = λ2[λF2 { type ap[f<:λ,x<:λ] = f ~ (f ~ x) }]
type SUCC = λ3[λF3 { type ap[n<:λ,f<:λ,x<:λ] = f ~ (n ~ f ~ x) }]
//type SUCC2b[n<:λ] = λ2[λF2 { type ap[f<:λ,x<:λ] = f ~ (n#eval ~ f ~ x) }]
//type SUCC2 = λ1[λF1 { type ap[n<:λ] = SUCC2b[n] }]

trait NF[a<:λ,b<:λ] extends λ {type eval = NF[a#eval,b#eval]; type ap[x<:λ] = NF[x,eval] }
type NFn = NF[∅,∅]
type NumEval[N<:λ] = N ~ NFn ~ α
def NumEq[A<:λ, B<:λ](implicit ev: NumEval[A]#eval =:= NumEval[B]#eval) = true

NumEq[N1, SUCC ~ N0]
NumEq[N2, SUCC ~ N1]

