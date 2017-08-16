module imobiliaria

----------------------------Assinaturas----------------------------
one sig ListaEspera{
	clientes: set Pessoa
}

sig Nome {
}

sig Pessoa{
	nome: one Nome
}

sig ClientePreferencial in Pessoa {
}

sig Quarto {
	morador: lone Pessoa
}

sig Suite  {
	moradorSuite: lone Pessoa
}

abstract sig Apartamento {
	quartos: set Quarto,
	suites: set Suite
}

sig Cobertura extends Apartamento {
} 

sig ApartamentoPequeno extends Apartamento {
}

sig ApartamentoGrande extends Apartamento {
}

----------------------------Fatos----------------------------

fact fato {
	#Apartamento = 6
	#ApartamentoPequeno = 3
	#ApartamentoGrande = 2
	#Cobertura = 1
	
	-- Definicao do numero de Quartos/Suites
	all a: ApartamentoPequeno | #quartosDoApartamento[a] = 1  and #suitesDoApartamento[a] = 1
	all a: ApartamentoGrande | #quartosDoApartamento[a] = 1 and #suitesDoApartamento[a] = 2
	all c: Cobertura | #quartosDoApartamento[c] = 0 and #suitesDoApartamento[c] = 3
    
	-- Todo nome so esta em uma pessoa
	all n:Nome, p:Pessoa, p1:Pessoa | n in p.nome and n in p1.nome => p = p1

	-- Todo nome faz parte de uma pessoa
	all n:Nome | one nomesEmConjuntoDeTodosOsNome[n]

	--Toda pessoa so esta em 1 quarto
	all p: Pessoa, q:Quarto, q1:Quarto | todaPessoaEmUmQuarto[p,q,q1]

	-- Todo quarto so esta em um apartamento
	all q: Quarto, a:Apartamento, a1:Apartamento | quartoSoEstaEmUmApt[q,a,a1]

	-- Todo quarto faz parte de um apartamento
	all q: Quarto |  one quartosEmConjuntoDeTodosOsQuartos[q]
	all s: Suite |  one suitesEmConjuntoDeTodasAsSuites[s]

	--Cliente ou esta em quarto ou na lista de espera 
	all p:Pessoa | clienteEstaEmQuartoOuListaEspera[p]

	-- Lista de espera só terá clientes se todos os Apartamentos estiverem alugados
	all a:Apartamento, l:ListaEspera | #pessoasDoAp[a] = 0 => #l.clientes = 0

	-- Moradores da cobertura sao preferenciais
	all c:Cobertura, s:Suite, p:Pessoa | p in s.moradorSuite and s in c.suites => p in ClientePreferencial
}

----------------------------Funcoes----------------------------

fun nomesEmConjuntoDeTodosOsNome[n:Nome]: set Pessoa {
	n.~nome
}

fun quartosEmConjuntoDeTodosOsQuartos[q:Quarto]: set Apartamento {
	q.~quartos
}

fun suitesEmConjuntoDeTodasAsSuites[s:Suite]: set Apartamento {
	s.~suites
}

fun suitesDoApartamento[a:Apartamento]: set Suite {
	a.suites
}

fun quartosDoApartamento[a:Apartamento]: set Quarto {
	a.quartos
}

fun pessoasDoAp[a:Apartamento]: set Pessoa {
	a.quartos.morador + a.suites.moradorSuite
}
----------------------------Predicados----------------------------

pred clienteEstaEmQuartoOuListaEspera[p:Pessoa] {
	one(p.~morador) and no(p.~clientes) and no(p.~moradorSuite) or (no(p.~morador) and one(p.~clientes) and no(p.~moradorSuite)) or (no(p.~morador) and no(p.~clientes) and one(p.~moradorSuite)) 
}

pred quartoSoEstaEmUmApt[q: Quarto, a:Apartamento, a1:Apartamento] {
	q in a.quartos and q in a1.quartos => a = a1
}

pred todaPessoaEmUmQuarto[p:Pessoa, q:Quarto, q1:Quarto] {
	p in q.morador and p in q1.morador => q = q1
}

----------------------------Asserts----------------------------

assert apartamentosCom2ou3Quartos {
	all a:Apartamento | #(a.quartos) = 1 and #(a.suites) = 1 or #(a.quartos) = 1 and #(a.suites) = 2
}

assert todoQuartoEstaEmUmApt {
	all q: Quarto |  #(q.~quartos) = 1
}

assert todaSuiteEstaEmUmApt {
	all s: Suite |  #(s.~suites) = 1
}

assert todaCoberturaPossui3Suites{
	all c:Cobertura | #(c.quartos) = 0 and #(c.suites) = 3
}

check apartamentosCom2ou3Quartos
check todoQuartoEstaEmUmApt
check todaSuiteEstaEmUmApt
check todaCoberturaPossui3Suites

pred show[]{}
run show for 30

