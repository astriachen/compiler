package syntax;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import lexical.LexicalAnalyzer;

public class LR1 {
	public String path = "syntax.txt";//�ķ�
	public String in_path = "lexical.txt";//�ʷ����������Ķ�Ԫ��
	public ArrayList<String> string_in = new ArrayList<String>();//�ʷ����������Ľ��
	public ArrayList<String> grammar = new ArrayList<String>();//�ķ�����ʽ

	public ArrayList<Map<String, String>> produce = new ArrayList<Map<String, String>>();//�������ʽ
	public ArrayList<Map<String, String>> produces = new ArrayList<Map<String, String>>();//��produce�Ĳ���ʽ��.���滻�ո�ķ�ʽ

	public ArrayList<String> terminal = new ArrayList<String>();//�ս������
	public ArrayList<String> nonTerminal = new ArrayList<String>();//���ս������

	public ArrayList<Map<String, Object>> DFA = new ArrayList<Map<String, Object>>();//���״̬ת�ƹ�ϵ
	public ArrayList<ArrayList<Map<String, Object>>> projectUnions = new ArrayList<ArrayList<Map<String, Object>>>();//��Ų���������״̬

	public ArrayList<Map<String, Object>> analyseTableAction = new ArrayList<Map<String, Object>>();//Action��
	public ArrayList<Map<String, Object>> analyseTableGoto = new ArrayList<Map<String, Object>>();//Goto��

	public Map<Object, Object> searchs = new HashMap<Object, Object>();//������
	private Stack<String> st_sym = new Stack<String>();//�������
	private Stack<Integer> st_state = new Stack<Integer>();//����״̬

	public ArrayList<String> readin() throws IOException{//����ʷ����������Ķ�Ԫ���ļ�lexical.txt
		ArrayList<String> str_in = new ArrayList<String>();
		File fin = new File(in_path);
		BufferedReader br=new BufferedReader(new FileReader(fin));

		String line;
		while((line = br.readLine()) != null){//���ж���
			String target[] = line.split("\t");
			if(target[0].equals("25")){
				str_in.add("id");
			}else if(target[0].equals("26")){
				str_in.add("num");
			}else{
				str_in.add(target[1]);//���ͼ��뵽������
			}
		}
		str_in.add("#");//���Ӹ�������
		br.close();
		return str_in;
	}

	public void readFile() throws IOException { //��ȡsyntax.txt���ķ���
		File file = new File(path);
		BufferedReader br=new BufferedReader(new FileReader(file));

		String line;
		while ((line = br.readLine()) != null)
		{
			grammar.add(line);
		}
		br.close();
	}

	public void spilt() { //�ַ��ָ������ʽ�ָ�
		String left, right;
		String[] temp;
		temp = grammar.get(0).split(" ");
		for (String s : temp)
			nonTerminal.add(s);//���뵽���ս��

		temp = grammar.get(1).split(" ");
		for (String s : temp)
			terminal.add(s);//���뵽�ս��

		for (int i = 2; i < grammar.size(); i++) {//�����ķ�����ʽ
			String line = grammar.get(i);
			String[] temp1;
			temp1 = line.split(" -> ");//���
			left = temp1[0];
			right = temp1[1];
			temp1 = right.split(" \\| ");//�����"|"�ı��ʽ
			for (String s : temp1) {
				Map<String, String> map = new HashMap<String, String>();
				map.put("left", left);//��ʾ���
				if (s.equals("$")){//���Ϊ�մ�
					s = "";
				}
				map.put("right", s);//��ʾ�Ҷ�
				produce.add(map);//��������
			}
		}
	}

	public void produceToProduces(){//ʹ�ô���ո�ķ������Ի���string
		for (Map<String, String> map : produce) {//����produce
			String left = map.get("left");
			String right = map.get("right");
			String part[] = right.split(" ");//���ո�ֿ�,������ȷ���Ҷ˺��м���
			String rtmp = null;

			for (int i = 0; i < part.length + 1; i++) {
				String newString = null;
				if (right.equals("")) {//Ϊ�գ�ֱ�ӱ�.
					newString = ".";
					i = 2;//ʹ��һ�ν�������Ϊ�Ҷ��Ѿ���ĩβ
				} else {
					if(i == 0) {//���������
						rtmp = right ;
						rtmp = "."+rtmp;
					} else if (i == part.length ) {//�������ұ�
						rtmp = right+".";
					} else {
						int pointpos = rtmp.indexOf(".");//��õ�ǰ.��λ��
						rtmp = rtmp.substring(0, pointpos)+rtmp.substring(pointpos+1);//��.ȥ��
						rtmp = rtmp.replaceFirst(" ", ".");//��һ��Ӧ����.��λ��
					}
					newString = rtmp;
				}
				Map<String, String> newMap = new HashMap<String, String>();//�������Ĳ���ʽ
				newMap.put("left", left);
				newMap.put("right", newString);
				//System.out.println(left+" -> "+newString);
				produces.add(newMap);
			}
		}
	}

	/**
	 * al ��ʾת�Ƶ��¸�״̬�Ĳ���ʽ���ṹ�а����������������ʼ������
	 * parent ��ʾǰһ״̬
	 */
	@SuppressWarnings("unchecked")
	public ArrayList<Map<String, Object>> createLR1DFA(ArrayList<Map<String, Object>> al, 
			ArrayList<Map<String, Object>> parent){//�����Զ���
		ArrayList<Map<String, Object>> Union = new ArrayList<Map<String, Object>>();//�½�һ��״̬

		if (al == null) {//״̬0ʱ���Ƚ����⣬��Ҫ��������
			al = new ArrayList<>();
			Map<String, Object> first = new HashMap<>();//��ʼ��״̬0�Ĺ���
			first.put("project", produces.get(0));//�׸�����ʽ
			//first.put("pos", 1);//��Ŀ����
			ArrayList<String> al2 = new ArrayList<>();//����ʽ��Ӧ���������������ж���
			al2.add("#");//�����������
			first.put("search", al2);
			al.add(first);//��ʼ������
		}
		for (Map<String, Object> project : al) {//��������al���߳�ʼ�����al,һ���ڱ�״̬��
			Union.add(project);//�������ʽ
		}

		int pos = 0;
		getClosure(pos,Union);//�ݹ����
		ArrayList<Map<String, Object>> next = new ArrayList<Map<String, Object>>();//���¸�״̬�Ĺ�����ϵ
		getEdge(Union, next);

		int addflag = 0;
		if (!projectUnions.contains(Union))//�����ڸ�״̬�����
		{
			projectUnions.add(Union);
			addflag = 1;
		}
		else {//����
			int temppos = projectUnions.indexOf(Union);
			Union = projectUnions.get(temppos);
		}

		for (Map<String, Object> map : next) {//next�б����һϵ��ת��
			Map<String, Object> node = new HashMap<String, Object>();
			node.put("begin", Union);
			node.put("edge", map.get("edge"));
			if (Union.equals(parent) || addflag == 0)//�ݹ鷵���жϣ��հ�������
				return Union;
			ArrayList<Map<String, Object>> nextUnion = createLR1DFA((ArrayList<Map<String, Object>>)
					map.get("value"), Union);//Ϊunion����һ��״̬
			node.put("end", nextUnion);//union���edge��ת��
			if (!DFA.contains(node))//����ת����
				DFA.add(node);
		}
		return Union;
	}

	/**
	 * 
	 * @param Union ��ǰ״̬
	 * @param next ��һ״̬
	 */
	@SuppressWarnings("unchecked")
	public void getEdge(ArrayList<Map<String, Object>> Union, ArrayList<Map<String, Object>> next) {//�Զ���״̬��ı�
		for (Map<String, Object> project : Union) {//�ҳ����п���ת�Ƶ�edge,���ҳ�ÿ��״̬�ﲻ��.Ϊ��������
			Map<String, String> pro = (Map<String, String>) project.get("project");//��õ�ǰ״̬����Ŀ��
			String right = pro.get("right");
			
			if (!right.endsWith(".")) {//��.�����ĵĲ�����
				int pointpos = right.indexOf(".");
				int spacepos = right.indexOf(" ",pointpos);//����ת�Ƶĵط�������.ת�Ƶ���һ���ո���S' ->.S ���S' ->S.
				String edge =null;
				if(spacepos == -1)//����ĩβ��ǰһλ��
					edge = right.substring(pointpos + 1);//��ת��edge��ֵΪ.ǰһ���ַ�����S' ->.S ���S' ->S.,edgeΪS
				else
					edge = right.substring(pointpos + 1, spacepos);//ȡһ�����ţ���E ->.E + T���E ->E.+ T,edgeΪE

				ArrayList<Map<String, Object>> newAl = null;//��ż�.���ַ����
				for (Map<String, Object> map : next) {
					if (map.get("edge").equals(edge)) {//����һ״̬next�в����Ѿ�����edge��Ӧ��״̬
						newAl = (ArrayList<Map<String, Object>>) map.get("value");//�����Ӧ����ŵ���edge��Ӧ��״̬���edgeΪE��E ->E.+ T��E ->E.- T��һ��
						break;
					}
				}

				if (newAl == null) {//���û�д�����Ӧ�ıߣ����½�һ����Ӧ��ϵ
					Map<String, Object> newMap = new HashMap<String, Object>();
					newAl = new ArrayList<>();
					newMap.put("edge", edge);
					newMap.put("value", newAl);
					next.add(newMap);
				}

				Map<String, Object> nextPros = new HashMap<>();//pro����һλ+search
				nextPros.put("project", produces.get(produces.indexOf(pro) + 1));//��ü�.�����Ŀ��
				ArrayList<String> newsea = new ArrayList<>();//��������
				for (String string : (ArrayList<String>) project.get("search"))
					newsea.add(string);//ֱ�Ӱ�search���Ӹ���״̬����
				nextPros.put("search", newsea);
				//nextPros.put("pos", project.get("pos"));
				newAl.add(nextPros);
			}
		}
	}

	@SuppressWarnings("unchecked")
	public void getClosure(int pos, ArrayList<Map<String, Object>> Union) {//�հ�
		while (true) {//�հ������ƶ���
			if (pos == Union.size())//��־����ĳ�αհ��������հ�size���䣬����pos+1�����հ����ٱ仯
				break;
			Map<String, Object> m = Union.get(pos);//��ĳһ��֪��Ŀ������
			pos++;
			Map<String, String> project = (Map<String, String>) m.get("project");//����ʽ��s'->.s��
			String right = project.get("right");
			if (right.endsWith("."))//�Ѿ������������׺Ϊ.
				continue;

			int pointPos = right.indexOf(".");//�ҵ�.��λ��,��s'->.s,����ֵΪ0
			int spacePos = right.indexOf(" ", pointPos);//��first����λ��,��s'->.s,����ֵΪ-1;E ->.E - T,����ֵΪ2
			String nextStr = null;//��Ҫ��հ����ַ���
			String searchStr = null;//����һ��Ҫ��ıհ����ַ���
			if(spacePos == -1)//���һ�����Դ����λ��
			{
				nextStr = right.substring(pointPos +1);//��s'->.s,����s
				searchStr = "";
			}
			else{
				nextStr = right.substring(pointPos +1,spacePos);//��E ->.E - T������E
				searchStr = right.substring(spacePos + 1);//E ->.E - T,���� - T
			}
			ArrayList<String> searchAl = new ArrayList<String>();//��������������

			if(searchStr == ""){}
			else{
				searchAl = (ArrayList<String>)solveFirstSet(searchStr);//��first��
			}

			if(searchAl.size() == 0){//first��Ϊ��
				for(String s :(ArrayList<String>) m.get("search")){ //���ǰ�����ķ��ַ��������յ������û�ҵ�first�� ��ô�������������
					if (!searchAl.contains(s))//�������ڣ������
						searchAl.add(s);
				}
			}

			if(terminal.contains(nextStr))//������ս�����򲻼���
				continue;
			for (Map<String, String> p : produce) {//����Ƿ��ս���������µĲ���ʽ
				String pl = p.get("left");
				if(pl.equals(nextStr)){//���
					Map<String, String> newPro = new HashMap<String, String>();
					newPro.put("left", pl);//�����µıհ������Ĳ���ʽ
					if (p.get("right").equals(""))
						newPro.put("right", ".");
					else
						newPro.put("right", "." + p.get("right"));

					ArrayList<String> newsearch = null;
					for (Map<String, Object> exits : Union) {
						Map<String, String> exitsPro = (Map<String, String>) exits.get("project");
						if (exitsPro.equals(newPro)) {//�¼�����Ѿ����ڣ�������������������Ҫ���
							newsearch = (ArrayList<String>) exits.get("search");
							break;
						}
					}
					if (newsearch == null) {
						Map<String, Object> newproj = new HashMap<String, Object>();//
						newsearch = new ArrayList<String>();

						newproj.put("project", newPro);
					//	newproj.put("pos", produce.indexOf(projectToProduce(newPro)));//ͨ��ԭʼ����ʽ��ò���ʽ��ţ���ӡʱ��״̬��
						newproj.put("search", newsearch);
						searchs.put(newPro, newsearch);//�������ʽ �Ͷ�Ӧ��������
						Union.add(newproj);
					}
					for (String s : searchAl)//������������
						if (!newsearch.contains(s))
							newsearch.add(s);
				}
			}
		}
	}

//	public Map<String, String> projectToProduce(Map<String, String> proj) {
//		String left = proj.get("left");
//		String right = proj.get("right");
//		Map<String, String> map = new HashMap<String, String>();
//		map.put("left", left);
//		map.put("right", right.replaceFirst("\\.", ""));//right�Ŀ�ʼ�ĵ��滻��"",��ȥ��
//		return map;
//	}

	public ArrayList<String> solveFirstSet(String str) {//first��
		if(str == "") return null;
		String nowstring = null;//һ��һ������
		String nextstring = null;
		int spos = -1;
		spos = str.indexOf(" ");//���ַ����л����ж����str="- T",����ֵΪ1
		if (spos == -1){//����������
			nowstring = str.substring(0);
			nextstring = "";
		}else{
			nowstring = str.substring(0, spos);//���ؿո�ǰһ���ַ�����str="- T"������-
			nextstring = str.substring(spos + 1);//���ؿո����ַ���
		}

		ArrayList<String> tmpal = new ArrayList<String>();
		for(Map<String, String> tmap : produce){//ɨ��ÿ������ʽ
			if(tmap.get("left").equals(nowstring)){//�ҵ���ǰҪ������ַ���
				if(tmap.get("right").equals("")){//��Ϊ��
					ArrayList<String> nextfirstal = solveFirstSet(nextstring);//first���ں�һ���ַ�������
					if(nextfirstal == null)continue;
					for(String temp_scale : nextfirstal)
						tmpal.add(temp_scale);
					continue;
				}
				String tright = tmap.get("right");
				String firstright[] = tright.split(" ");
				if (firstright[0].equals(nowstring))continue;
				ArrayList<String> nextfirstAL = solveFirstSet(tright);
				for(String temp_scale : nextfirstAL){
					tmpal.add(temp_scale);
				}
			}
		}
		if(terminal.contains(nowstring))
			tmpal.add(nowstring);//����first��
		return tmpal;
	}

	@SuppressWarnings("unchecked")
	public void printProjectsUnions() {//�����Ŀ����
		int count = 0;
		for (ArrayList<Map<String, Object>> al : projectUnions) {//����������Ŀ��
			System.out.println("\n--------I" + count++ + "-------");
			for (Map<String, Object> map : al) {
				Map<String, String> pro = (Map<String, String>) map.get("project");
				System.out.print(pro.get("left") + " -> " + pro.get("right"));
				if (map.containsKey("search")) {
					System.out.print(" , " + map.get("search"));
				}
				System.out.println();
			}
			System.out.println();
		}
	}

	@SuppressWarnings("unchecked")
	public void createLR1AnalyseTable() {//����������
		int terminalCount = terminal.size();
		int nonterminalCount = nonTerminal.size();
		int stateCount = projectUnions.size();//״̬����
		analyseTableAction.clear();
		analyseTableGoto.clear();
		
		for (int i = 0; i < stateCount; i++) {//һ��һ��״̬���
			ArrayList<Map<String, Object>> begin = projectUnions.get(i);//����ÿ��״̬

			//action����ƽ���
			for (int j = 0; j < terminalCount; j++) {
				for (Map<String, Object> dfa : DFA) {//���edge���ս��
					if (dfa.get("begin").equals(begin)&& dfa.get("edge").equals(terminal.get(j))) {//��ʼ״̬��ͬ���Ҷ�Ӧ�ս��
						ArrayList<Map<String, Object>> end = (ArrayList<Map<String, Object>>) dfa.get("end");//��һ��union
						int endPos = projectUnions.indexOf(end);//������һ��union��projectunions�е�λ��
						Map<String, Object> newMap = new HashMap<>();
						newMap.put("state", i);
						newMap.put("terminal", terminal.get(j));
						ArrayList<String> al = (ArrayList<String>) newMap.get("value");//���������ֵ
						if (al == null)//�п��ܲ�����ͻ���ж��ֵ
							al = new ArrayList<String>();
						al.add("S" + endPos);//����ת�Ƶ��ĸ�״̬
						newMap.put("value", al);
						analyseTableAction.add(newMap);
					}
				}
			}

			//action��Ĺ�Լ��
			for (Map<String, Object> map : begin) {//��Լ,����״̬�е�ÿ������ʽ
				Map<String, String> pro = (Map<String, String>) map.get("project");
				String right = pro.get("right");
				String left = pro.get("left");
				ArrayList<String> search = (ArrayList<String>) map.get("search");
				if (right.endsWith(".")) {//��Լ
					Map<String, String> prod = new HashMap<String, String>();
					prod.put("right", right.replaceFirst("\\.", ""));//ȥ��.
					prod.put("left", left);
					for (String se : search) {//Ϊÿһ���������е�Ԫ����ӹ�Լ����
						Map<String, Object> newMap = null;
						ArrayList<String> al = null;
						for (Map<String, Object> temp : analyseTableAction) {//�ж������ƽ�-��Լ��ͻ����Լ-��Լ��ͻ
							if (temp.get("state").equals(i)&& temp.get("terminal").equals(se)) {
								newMap = temp;
								al = (ArrayList<String>) temp.get("value");
								break;
							}
						}
						if (newMap == null) {//û�г�ͻ
							newMap = new HashMap<>();
							newMap.put("state", i);
							newMap.put("terminal", se);
							al = new ArrayList<String>();
							newMap.put("value", al);
							analyseTableAction.add(newMap);
						}

						if (produce.indexOf(prod) == 0) {//����ǵ�0������ʽ
							al.add("acc");//������
						} else {
							int pos = produce.indexOf(prod);//���յڼ�������ʽ��Լ
							al.add("r" + (pos + 1));//��1��ʼ����
						}
					}
				}
			}
			for (int j = 1; j < nonterminalCount; j++) {//goto��
				for (Map<String, Object> dfa : DFA) {//����
					if (dfa.get("begin").equals(begin)&& dfa.get("edge").equals(nonTerminal.get(j))) {//edgeΪ���ս��
						ArrayList<Map<String, Object>> end = (ArrayList<Map<String, Object>>) dfa.get("end");//��һ��״̬
						int endPos = projectUnions.indexOf(end);//״̬���
						Map<String, Object> newMap = new HashMap<String, Object>();
						newMap.put("state", i);
						newMap.put("terminal", nonTerminal.get(j));
						newMap.put("value", endPos);
						analyseTableGoto.add(newMap);
					}
				}
			}
		}
	}

	@SuppressWarnings("unchecked")
	public boolean isLR1() {
		boolean isLR1 = true;
		for (Map<String, Object> map : analyseTableAction) {//����������value��al��ֹһ��
			ArrayList<String> al = (ArrayList<String>) map.get("value");
			if (al.size() > 1) {
				isLR1 = false;
				break;
			}
		}
		return isLR1;
	}

	@SuppressWarnings("unchecked")
	public void printTable() {//������������ڱ�̫�󣬷�action����goto��ֱ����
		int terminalCount = terminal.size(); //�ս��
		int nonterminalCount = nonTerminal.size(); //���ս��
		int stateCount = projectUnions.size();

		System.out.println();
		System.out.print("-----------------Action��----------------\n");
		System.out.print("state   action\n     ");
		System.out.println();
		for (int i = 0; i < terminalCount; i++)//��ӡ�����ս��
			System.out.print("\t" + terminal.get(i));
		System.out.print("\t#\n");//�����������
		for (int i = 0; i < stateCount; i++) {
			System.out.print(i + "\t");
			for (int j = 0; j < terminalCount + 1; j++) {
				String temp;
				if (j != terminalCount)//�������ս��
					temp = terminal.get(j);
				else//���
					temp = "#";
				
				int flag = -1;
				for (Map<String, Object> map : analyseTableAction) {
					if (map.get("state").equals(i)&& map.get("terminal").equals(temp)) {
						ArrayList<String> al = (ArrayList<String>) map.get("value");
						for (int k = 0; k < al.size(); k++) {
							if (k == 0)
								System.out.print(" " + al.get(k));
							if (k > 0)//�г�ͻ�����
								System.out.print("," + al.get(k));
							if (k == al.size() - 1)
								System.out.print("  ");
						}
						flag = 1;
					}
				}
				if (flag == -1)//û����һ��
					System.out.print("\t");
			}
			System.out.println();
		}

		System.out.println();
		System.out.print("----------------GoTo��---------------\n");
		System.out.print("state  goto\n     ");
		System.out.println();
		
		for (int i = 1; i < nonterminalCount; i++)
			System.out.print("\t" + nonTerminal.get(i));
		System.out.println();
		for (int i = 0; i < stateCount; i++) {
			System.out.print(i + "\t");
			for (int j = 1; j < nonterminalCount; j++) {
				String temp = nonTerminal.get(j);

				int flag = -1;
				for (Map<String, Object> map : analyseTableGoto) {
					if (map.get("state").equals(i)
							&& map.get("terminal").equals(temp)) {
						System.out.print(map.get("value") + "\t");
						flag = 1;
					}
				}
				if (flag == -1)//û����һ��
					System.out.print(" \t");
			}
			System.out.println();
		}
		System.out.println();
		System.out.print("----------------�������̣�---------------\n");
		System.out.print("����----״̬ջ--------����ջ----------���봮--------����-\n");
		System.out.println();
	}

	public void printline(int i, String s_in, String kind, Map<String,String> prodc){//����������̵�ÿһ��
		System.out.print(i+"\t");//��ӡÿ�����
		Stack<String> tmp_st = new Stack<String>();
		Stack<Integer> tmp_stk = new Stack<Integer>();

		String temp_str = null;
		int temp_int = 0;
		while(!st_state.empty()){//���ջ����������
			temp_int = st_state.pop();
			System.out.print(temp_int+" ");
			tmp_stk.push(temp_int);//��ʱ���
		}
		System.out.print("\t");

		while(!tmp_stk.empty()){
			temp_int = tmp_stk.pop();
			st_state.push(temp_int);//�ָ�ջ
		}
		while(!st_sym.empty()){
			temp_str = st_sym.pop();
			System.out.print(temp_str+" ");
			tmp_st.push(temp_str);
		}
		System.out.print("\t");

		while(!tmp_st.empty()){
			temp_str = tmp_st.pop();
			st_sym.push(temp_str);
		}
		System.out.print(s_in+"\t");

		if(kind == "S"){
			System.out.print("����\n");
		}else if(kind == "r"){
			System.out.print("��");
			System.out.print(prodc.get("left")+" -> "+prodc.get("right"));
			System.out.print("��Լ\n");
		}else{
			System.out.print("����\n");
		}
	}

	@SuppressWarnings("unchecked")
	public boolean isShiBie() {//��ӡʱ����ÿ������
		boolean shiBie=true;
		this.st_state.push(0);//��ʼ��ջ
		this.st_sym.push("#");
		int i=1;//����
		
		for (String tmp_str : this.string_in) {//���������
			if(!tmp_str.equals("#")&&!this.terminal.contains(tmp_str)) {
				System.out.println("�����ڵ��ս��"+tmp_str);
				continue;
			}
			
			int tmp_flag=1;//��־��ǰ����������Ƿ����
			while(tmp_flag==1) {
				int tmp_state=this.st_state.peek();//��ȡջ��״̬
				for (Map<String, Object> tmp_map : this.analyseTableAction) {//��Ӧ����Action������
					if(tmp_map.get("state").equals(tmp_state) && tmp_map.get("terminal").equals(tmp_str)) {
						ArrayList<String> tmp_al = (ArrayList<String>) tmp_map.get("value");//ȡ�����������������
						
						if(tmp_al==null) {//����error
							System.out.println("���򲻱�ʶ��");
							shiBie=false;
							return shiBie;
						} else {//����ʶ��
							String firstChar=tmp_al.get(0).substring(0, 1);//�õ���һ����ĸ
							if(tmp_al.get(0).equals("acc")){//ʶ��ɹ�
								this.st_state.pop();
								this.st_sym.pop();
								this.printline(i,tmp_str,"acc",null);
								i++;
								return shiBie;//�ɹ�
							}
							
							if(firstChar.equals("S")) {//�ƽ�
								int nextState=Integer.parseInt(tmp_al.get(0).substring(1));//�õ���һ��״̬
								this.st_state.push(nextState);//��ջ
								this.st_sym.push(tmp_str);
								tmp_flag=0;//�����˳���ǰ��������
								this.printline(i,tmp_str,"S",null);
								i++;
								break;
							} else if(firstChar.equals("r")) {//��Լ
								int num=Integer.parseInt(tmp_al.get(0).substring(1));
								Map<String, String> tmp_pro=this.produce.get(num-1);//�õ������ĸ�����ʽ��Լ
								String tmp_right=tmp_pro.get("right");
								String[] temp_str;
								temp_str=tmp_right.split(" ");//���Ŀ�����ʽ
								int count=temp_str.length;//����
								if(tmp_right==""){//�ղ���ʽ
									count=0;
								}
								while(count!=0){//δ��Լ��
									this.st_state.pop();
									this.st_sym.pop();
									count--;
								}
								this.st_sym.push(tmp_pro.get("left"));//����ʽ���ѹջ
								int tmp_stat=this.st_state.peek();//��ʱ����ջ��һ���Ƿ��ս��
								
								//��Ҫgoto����Ӧ��ѹ��״̬ջ
								for(Map<String,Object> tmp_goto : this.analyseTableGoto){//����goto��
									if(tmp_goto.get("state").equals(tmp_stat) && tmp_goto.get("terminal").equals(this.st_sym.peek())){
										int goto_state = 1000000;
										goto_state = (int)tmp_goto.get("value");
										if(goto_state == 1000000 || goto_state == 0){
											shiBie=false;
											return shiBie;
										}else{
											this.st_state.push(goto_state);
											break;
										}
									}
								}
								this.printline(i, tmp_str, "r", tmp_pro);
								i++;
								break;
							}
						}
					}
				}
			}
		}
		return shiBie;
	}

	public void createLR1() throws IOException{
		this.string_in=this.readin();
		this.readFile();
		this.spilt();
		this.produceToProduces();
		this.projectUnions.clear();//���
		this.DFA.clear();
		this.createLR1DFA(null, null);//��ʼʱ״̬��û�е���һ��״̬�Ĳ���ʽ���Ҳ�����ǰһ״̬
		this.createLR1AnalyseTable();
		if (!isLR1()) {//δ�ɹ����������������ڳ�ͻ
			System.out.println("������LR1�ķ�!");
			return;
		}
		this.printProjectsUnions();//��Ŀ����
		this.printTable();
		if(this.isShiBie()){
			System.out.println("�ɹ�ʶ��ó���");
		}else{
			System.out.println("�ķ�����ʶ��ó���");
		}
	}
	public static void main(String[] args) throws Exception {
		LexicalAnalyzer la=new LexicalAnalyzer();
		la.read();
		la.write();
		LR1 lr=new LR1();
		lr.createLR1();
	}
}
