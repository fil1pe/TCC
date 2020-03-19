# TCC
Repositório que contém os documentos e implementações de meu TCC.

## Autômato finito determinístico

Um autômato finito determinístico (AFD) é definido por este trabalho como a seguinte quádrupla:

![Quádrupla AFD](https://github.com/fil1pe/TCC/blob/master/Imagens/dfa.png)

em que:

![Conjunto de estados](https://github.com/fil1pe/TCC/blob/master/Imagens/state_set.png) é o conjunto de estados e ![Estado zero](https://github.com/fil1pe/TCC/blob/master/Imagens/0.png) é o estado inicial

![Conjunto de eventos](https://github.com/fil1pe/TCC/blob/master/Imagens/event_set.png) é o conjunto de eventos

![Função de transição](https://github.com/fil1pe/TCC/blob/master/Imagens/transition_function.png) é a função de transição

![Função de estados marcados](https://github.com/fil1pe/TCC/blob/master/Imagens/marked_states_function.png) é a função de estados marcados

As funções são definidas com o conjunto dos números naturais, e não com os próprios conjuntos de estados e eventos, para facilitar a implementação. Como os conjuntos de estados e eventos são subconjuntos dos naturais, quaisquer transições partindo ou chegando a estados e eventos indefinidos são desconsideradas pela função de transição estendida. Ademais, os dois primeiros elementos da quádrupla são naturais. A subtração por um, nesse caso, é para impedir que conjuntos vazios sejam instanciados.
