module imobiliaria

one sig ListaEspera{
	clientes: set Pessoa
}
abstract sig Apartamento {
	quartos: set Quarto
}
sig Suite extends Quarto{
}

sig Cobertura extends Apartamento {
}

sig ApartamentoPequeno extends Apartamento {
}

sig ApartamentoGrande extends Apartamento {
}


sig Quarto {
	morador: Pessoa
}

sig Pessoa{}

sig ClientePreferencial in Pessoa {}

fact fato {
	#Apartamento = 6
	#ApartamentoPequeno = 3
	#ApartamentoGrande = 2
	#Cobertura = 1
	
	//Todo apartamento tem um conjunto de quartos
	all a: ApartamentoPequeno | #quartosDoApartamento[a] = 2  
	all a: ApartamentoGrande | #quartosDoApartamento[a] = 3 
	//Todo quarto pode ter um morador
	all q: Quarto | temMorador[q]
    //Todo quarto so esta em 1 apartamento
	all q: Quarto, a:Apartamento, a1:Apartamento | quartoSoEstaEmUmApt[q,a,a1]
	//Todo quarto faz parte de um apartamento
	all q: Quarto |  one quartosEmConjuntoDeTodosOsQuartos[q]
	//Toda pessoa so esta em 1 quarto
	all p: Pessoa, q:Quarto, q1:Quarto | p in q.morador and p in q1.morador => q = q1
	//cliente ou esta em quarto ou na lista de espera 
	all l:ListaEspera, q:Quarto | clienteEstaEmQuartoOuListaEspera[l, q]
	//toda pessoa esta em lista de espera ou em quarto
	all p:Pessoa | one(p.~morador) or one(p.~clientes)
	//toda cobertura tem 3 quartos
	all c:Cobertura | #quartosDaCobertura[c] = 3


}

fun quartosEmConjuntoDeTodosOsQuartos[q:Quarto]: set Apartamento {
	q.~quartos
}

fun quartosDoApartamento[a:Apartamento]: set Quarto {
	a.quartos
}

fun quartosDaCobertura[c:Cobertura]: set Quarto {
	c.quartos
}


pred clienteEstaEmQuartoOuListaEspera[l:ListaEspera, q:Quarto] {
	no(l.clientes & q.morador)
}


pred temMorador[q:Quarto] {
	some q.morador
}

pred quartoSoEstaEmUmApt[q: Quarto, a:Apartamento, a1:Apartamento] {
	q in a.quartos and q in a1.quartos => a = a1
}

assert apartamentosCom2ou3Quartos {
	all a:Apartamento | #(a.quartos) = 2 or #(a.quartos) = 3
}

assert todoQuartoEstaEmUmApt {
	all q: Quarto |  #(q.~quartos) = 1
}

assert todaCoberturaPossui3Quartos{
	all c:Cobertura | #(c.quartos) = 3
}

check apartamentosCom2ou3Quartos
check todoQuartoEstaEmUmApt
check todaCoberturaPossui3Quartos

pred show[]{}
run show for 30

