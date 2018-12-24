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
	public String path = "syntax.txt";//文法
	public String in_path = "lexical.txt";//词法分析产生的二元组
	public ArrayList<String> string_in = new ArrayList<String>();//词法分析产生的结果
	public ArrayList<String> grammar = new ArrayList<String>();//文法产生式

	public ArrayList<Map<String, String>> produce = new ArrayList<Map<String, String>>();//保存产生式
	public ArrayList<Map<String, String>> produces = new ArrayList<Map<String, String>>();//对produce的产生式加.按替换空格的方式

	public ArrayList<String> terminal = new ArrayList<String>();//终结符集合
	public ArrayList<String> nonTerminal = new ArrayList<String>();//非终结符集合

	public ArrayList<Map<String, Object>> DFA = new ArrayList<Map<String, Object>>();//存放状态转移关系
	public ArrayList<ArrayList<Map<String, Object>>> projectUnions = new ArrayList<ArrayList<Map<String, Object>>>();//存放产生的所有状态

	public ArrayList<Map<String, Object>> analyseTableAction = new ArrayList<Map<String, Object>>();//Action表
	public ArrayList<Map<String, Object>> analyseTableGoto = new ArrayList<Map<String, Object>>();//Goto表

	public Map<Object, Object> searchs = new HashMap<Object, Object>();//搜索集
	private Stack<String> st_sym = new Stack<String>();//存入符号
	private Stack<Integer> st_state = new Stack<Integer>();//存入状态

	public ArrayList<String> readin() throws IOException{//读入词法分析产生的二元组文件lexical.txt
		ArrayList<String> str_in = new ArrayList<String>();
		File fin = new File(in_path);
		BufferedReader br=new BufferedReader(new FileReader(fin));

		String line;
		while((line = br.readLine()) != null){//按行读入
			String target[] = line.split("\t");
			if(target[0].equals("25")){
				str_in.add("id");
			}else if(target[0].equals("26")){
				str_in.add("num");
			}else{
				str_in.add(target[1]);//类型加入到集合中
			}
		}
		str_in.add("#");//最后加个结束符
		br.close();
		return str_in;
	}

	public void readFile() throws IOException { //读取syntax.txt（文法）
		File file = new File(path);
		BufferedReader br=new BufferedReader(new FileReader(file));

		String line;
		while ((line = br.readLine()) != null)
		{
			grammar.add(line);
		}
		br.close();
	}

	public void spilt() { //字符分割，即产生式分割
		String left, right;
		String[] temp;
		temp = grammar.get(0).split(" ");
		for (String s : temp)
			nonTerminal.add(s);//加入到非终结符

		temp = grammar.get(1).split(" ");
		for (String s : temp)
			terminal.add(s);//加入到终结符

		for (int i = 2; i < grammar.size(); i++) {//处理文法产生式
			String line = grammar.get(i);
			String[] temp1;
			temp1 = line.split(" -> ");//拆分
			left = temp1[0];
			right = temp1[1];
			temp1 = right.split(" \\| ");//处理带"|"的表达式
			for (String s : temp1) {
				Map<String, String> map = new HashMap<String, String>();
				map.put("left", left);//表示左端
				if (s.equals("$")){//如果为空串
					s = "";
				}
				map.put("right", s);//表示右端
				produce.add(map);//保存起来
			}
		}
	}

	public void produceToProduces(){//使用代替空格的方法可以划分string
		for (Map<String, String> map : produce) {//遍历produce
			String left = map.get("left");
			String right = map.get("right");
			String part[] = right.split(" ");//按空格分开,就是来确定右端含有几项
			String rtmp = null;

			for (int i = 0; i < part.length + 1; i++) {
				String newString = null;
				if (right.equals("")) {//为空，直接变.
					newString = ".";
					i = 2;//使得一次结束，因为右端已经到末尾
				} else {
					if(i == 0) {//加在最左边
						rtmp = right ;
						rtmp = "."+rtmp;
					} else if (i == part.length ) {//加在最右边
						rtmp = right+".";
					} else {
						int pointpos = rtmp.indexOf(".");//获得当前.的位置
						rtmp = rtmp.substring(0, pointpos)+rtmp.substring(pointpos+1);//把.去掉
						rtmp = rtmp.replaceFirst(" ", ".");//下一个应当加.的位置
					}
					newString = rtmp;
				}
				Map<String, String> newMap = new HashMap<String, String>();//处理过后的产生式
				newMap.put("left", left);
				newMap.put("right", newString);
				//System.out.println(left+" -> "+newString);
				produces.add(newMap);
			}
		}
	}

	/**
	 * al 表示转移到下个状态的产生式（结构中包含搜索集），起初始化作用
	 * parent 表示前一状态
	 */
	@SuppressWarnings("unchecked")
	public ArrayList<Map<String, Object>> createLR1DFA(ArrayList<Map<String, Object>> al, 
			ArrayList<Map<String, Object>> parent){//创建自动机
		ArrayList<Map<String, Object>> Union = new ArrayList<Map<String, Object>>();//新建一个状态

		if (al == null) {//状态0时，比较特殊，需要单独处理
			al = new ArrayList<>();
			Map<String, Object> first = new HashMap<>();//初始化状态0的过程
			first.put("project", produces.get(0));//首个产生式
			//first.put("pos", 1);//项目集号
			ArrayList<String> al2 = new ArrayList<>();//产生式对应的搜索集，可能有多项
			al2.add("#");//加入结束符号
			first.put("search", al2);
			al.add(first);//初始化结束
		}
		for (Map<String, Object> project : al) {//遍历来的al或者初始化后的al,一定在本状态中
			Union.add(project);//加入产生式
		}

		int pos = 0;
		getClosure(pos,Union);//递归产生
		ArrayList<Map<String, Object>> next = new ArrayList<Map<String, Object>>();//与下个状态的关联关系
		getEdge(Union, next);

		int addflag = 0;
		if (!projectUnions.contains(Union))//不存在该状态则添加
		{
			projectUnions.add(Union);
			addflag = 1;
		}
		else {//存在
			int temppos = projectUnions.indexOf(Union);
			Union = projectUnions.get(temppos);
		}

		for (Map<String, Object> map : next) {//next中保存的一系列转移
			Map<String, Object> node = new HashMap<String, Object>();
			node.put("begin", Union);
			node.put("edge", map.get("edge"));
			if (Union.equals(parent) || addflag == 0)//递归返回判断，闭包不增大
				return Union;
			ArrayList<Map<String, Object>> nextUnion = createLR1DFA((ArrayList<Map<String, Object>>)
					map.get("value"), Union);//为union接下一个状态
			node.put("end", nextUnion);//union相对edge的转换
			if (!DFA.contains(node))//放入转移中
				DFA.add(node);
		}
		return Union;
	}

	/**
	 * 
	 * @param Union 当前状态
	 * @param next 下一状态
	 */
	@SuppressWarnings("unchecked")
	public void getEdge(ArrayList<Map<String, Object>> Union, ArrayList<Map<String, Object>> next) {//自动机状态间的边
		for (Map<String, Object> project : Union) {//找出所有可以转移的edge,即找出每个状态里不以.为结束的项
			Map<String, String> pro = (Map<String, String>) project.get("project");//获得当前状态的项目集
			String right = pro.get("right");
			
			if (!right.endsWith(".")) {//以.结束的的不考虑
				int pointpos = right.indexOf(".");
				int spacepos = right.indexOf(" ",pointpos);//可以转移的地方，即把.转移到下一个空格，如S' ->.S 变成S' ->S.
				String edge =null;
				if(spacepos == -1)//到了末尾的前一位置
					edge = right.substring(pointpos + 1);//该转移edge上值为.前一个字符，如S' ->.S 变成S' ->S.,edge为S
				else
					edge = right.substring(pointpos + 1, spacepos);//取一个符号，如E ->.E + T变成E ->E.+ T,edge为E

				ArrayList<Map<String, Object>> newAl = null;//存放加.后字符的项集
				for (Map<String, Object> map : next) {
					if (map.get("edge").equals(edge)) {//在下一状态next中查找已经存在edge对应的状态
						newAl = (ArrayList<Map<String, Object>>) map.get("value");//则把相应的项放到该edge对应的状态里，即edge为E，E ->E.+ T和E ->E.- T放一起
						break;
					}
				}

				if (newAl == null) {//如果没有存在相应的边，则新建一个对应关系
					Map<String, Object> newMap = new HashMap<String, Object>();
					newAl = new ArrayList<>();
					newMap.put("edge", edge);
					newMap.put("value", newAl);
					next.add(newMap);
				}

				Map<String, Object> nextPros = new HashMap<>();//pro右移一位+search
				nextPros.put("project", produces.get(produces.indexOf(pro) + 1));//获得加.后的项目集
				ArrayList<String> newsea = new ArrayList<>();//新搜索集
				for (String string : (ArrayList<String>) project.get("search"))
					newsea.add(string);//直接把search集从父亲状态复制
				nextPros.put("search", newsea);
				//nextPros.put("pos", project.get("pos"));
				newAl.add(nextPros);
			}
		}
	}

	@SuppressWarnings("unchecked")
	public void getClosure(int pos, ArrayList<Map<String, Object>> Union) {//闭包
		while (true) {//闭包，类似队列
			if (pos == Union.size())//标志经过某次闭包操作，闭包size不变，但是pos+1，即闭包不再变化
				break;
			Map<String, Object> m = Union.get(pos);//从某一已知项目集遍历
			pos++;
			Map<String, String> project = (Map<String, String>) m.get("project");//产生式（s'->.s）
			String right = project.get("right");
			if (right.endsWith("."))//已经处理结束，后缀为.
				continue;

			int pointPos = right.indexOf(".");//找到.的位置,如s'->.s,返回值为0
			int spacePos = right.indexOf(" ", pointPos);//求first集的位置,如s'->.s,返回值为-1;E ->.E - T,返回值为2
			String nextStr = null;//需要求闭包的字符串
			String searchStr = null;//再下一次要求的闭包的字符串
			if(spacePos == -1)//最后一个可以处理的位置
			{
				nextStr = right.substring(pointPos +1);//如s'->.s,返回s
				searchStr = "";
			}
			else{
				nextStr = right.substring(pointPos +1,spacePos);//如E ->.E - T，返回E
				searchStr = right.substring(spacePos + 1);//E ->.E - T,返回 - T
			}
			ArrayList<String> searchAl = new ArrayList<String>();//用来保存搜索集

			if(searchStr == ""){}
			else{
				searchAl = (ArrayList<String>)solveFirstSet(searchStr);//求first集
			}

			if(searchAl.size() == 0){//first集为空
				for(String s :(ArrayList<String>) m.get("search")){ //如果前部分文法字符串（即空的情况）没找到first集 那么看后面的搜索符
					if (!searchAl.contains(s))//若不存在，则加入
						searchAl.add(s);
				}
			}

			if(terminal.contains(nextStr))//如果是终结符，则不加入
				continue;
			for (Map<String, String> p : produce) {//如果是非终结符，加入新的产生式
				String pl = p.get("left");
				if(pl.equals(nextStr)){//左端
					Map<String, String> newPro = new HashMap<String, String>();
					newPro.put("left", pl);//加入新的闭包产生的产生式
					if (p.get("right").equals(""))
						newPro.put("right", ".");
					else
						newPro.put("right", "." + p.get("right"));

					ArrayList<String> newsearch = null;
					for (Map<String, Object> exits : Union) {
						Map<String, String> exitsPro = (Map<String, String>) exits.get("project");
						if (exitsPro.equals(newPro)) {//新加入的已经存在，处理搜索集，可能需要添加
							newsearch = (ArrayList<String>) exits.get("search");
							break;
						}
					}
					if (newsearch == null) {
						Map<String, Object> newproj = new HashMap<String, Object>();//
						newsearch = new ArrayList<String>();

						newproj.put("project", newPro);
					//	newproj.put("pos", produce.indexOf(projectToProduce(newPro)));//通过原始产生式获得产生式编号，打印时的状态号
						newproj.put("search", newsearch);
						searchs.put(newPro, newsearch);//保存产生式 和对应的搜索集
						Union.add(newproj);
					}
					for (String s : searchAl)//把搜索集放入
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
//		map.put("right", right.replaceFirst("\\.", ""));//right的开始的点替换成"",即去掉
//		return map;
//	}

	public ArrayList<String> solveFirstSet(String str) {//first集
		if(str == "") return null;
		String nowstring = null;//一个一个处理
		String nextstring = null;
		int spos = -1;
		spos = str.indexOf(" ");//该字符串中还含有多项，如str="- T",返回值为1
		if (spos == -1){//处理其他的
			nowstring = str.substring(0);
			nextstring = "";
		}else{
			nowstring = str.substring(0, spos);//返回空格前一个字符，如str="- T"，返回-
			nextstring = str.substring(spos + 1);//返回空格后的字符串
		}

		ArrayList<String> tmpal = new ArrayList<String>();
		for(Map<String, String> tmap : produce){//扫描每个产生式
			if(tmap.get("left").equals(nowstring)){//找到当前要处理的字符串
				if(tmap.get("right").equals("")){//若为空
					ArrayList<String> nextfirstal = solveFirstSet(nextstring);//first集在后一个字符串里求
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
			tmpal.add(nowstring);//加入first集
		return tmpal;
	}

	@SuppressWarnings("unchecked")
	public void printProjectsUnions() {//输出项目集族
		int count = 0;
		for (ArrayList<Map<String, Object>> al : projectUnions) {//遍历整个项目集
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
	public void createLR1AnalyseTable() {//创建分析表
		int terminalCount = terminal.size();
		int nonterminalCount = nonTerminal.size();
		int stateCount = projectUnions.size();//状态个数
		analyseTableAction.clear();
		analyseTableGoto.clear();
		
		for (int i = 0; i < stateCount; i++) {//一个一个状态填表
			ArrayList<Map<String, Object>> begin = projectUnions.get(i);//遍历每个状态

			//action表的移进项
			for (int j = 0; j < terminalCount; j++) {
				for (Map<String, Object> dfa : DFA) {//如果edge是终结符
					if (dfa.get("begin").equals(begin)&& dfa.get("edge").equals(terminal.get(j))) {//开始状态相同，且对应终结符
						ArrayList<Map<String, Object>> end = (ArrayList<Map<String, Object>>) dfa.get("end");//下一个union
						int endPos = projectUnions.indexOf(end);//返回下一个union在projectunions中的位置
						Map<String, Object> newMap = new HashMap<>();
						newMap.put("state", i);
						newMap.put("terminal", terminal.get(j));
						ArrayList<String> al = (ArrayList<String>) newMap.get("value");//表内填入的值
						if (al == null)//有可能产生冲突，有多个值
							al = new ArrayList<String>();
						al.add("S" + endPos);//移入转移到哪个状态
						newMap.put("value", al);
						analyseTableAction.add(newMap);
					}
				}
			}

			//action表的规约项
			for (Map<String, Object> map : begin) {//归约,遍历状态中的每个产生式
				Map<String, String> pro = (Map<String, String>) map.get("project");
				String right = pro.get("right");
				String left = pro.get("left");
				ArrayList<String> search = (ArrayList<String>) map.get("search");
				if (right.endsWith(".")) {//规约
					Map<String, String> prod = new HashMap<String, String>();
					prod.put("right", right.replaceFirst("\\.", ""));//去除.
					prod.put("left", left);
					for (String se : search) {//为每一个搜索集中的元素添加规约表项
						Map<String, Object> newMap = null;
						ArrayList<String> al = null;
						for (Map<String, Object> temp : analyseTableAction) {//判断有无移近-规约冲突，规约-规约冲突
							if (temp.get("state").equals(i)&& temp.get("terminal").equals(se)) {
								newMap = temp;
								al = (ArrayList<String>) temp.get("value");
								break;
							}
						}
						if (newMap == null) {//没有冲突
							newMap = new HashMap<>();
							newMap.put("state", i);
							newMap.put("terminal", se);
							al = new ArrayList<String>();
							newMap.put("value", al);
							analyseTableAction.add(newMap);
						}

						if (produce.indexOf(prod) == 0) {//如果是第0条产生式
							al.add("acc");//结束符
						} else {
							int pos = produce.indexOf(prod);//按照第几条产生式规约
							al.add("r" + (pos + 1));//从1开始排序
						}
					}
				}
			}
			for (int j = 1; j < nonterminalCount; j++) {//goto表
				for (Map<String, Object> dfa : DFA) {//遍历
					if (dfa.get("begin").equals(begin)&& dfa.get("edge").equals(nonTerminal.get(j))) {//edge为非终结符
						ArrayList<Map<String, Object>> end = (ArrayList<Map<String, Object>>) dfa.get("end");//下一个状态
						int endPos = projectUnions.indexOf(end);//状态编号
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
		for (Map<String, Object> map : analyseTableAction) {//如果分析表的value的al不止一项
			ArrayList<String> al = (ArrayList<String>) map.get("value");
			if (al.size() > 1) {
				isLR1 = false;
				break;
			}
		}
		return isLR1;
	}

	@SuppressWarnings("unchecked")
	public void printTable() {//输出分析表，由于表太大，分action表与goto表分别输出
		int terminalCount = terminal.size(); //终结符
		int nonterminalCount = nonTerminal.size(); //非终结符
		int stateCount = projectUnions.size();

		System.out.println();
		System.out.print("-----------------Action表----------------\n");
		System.out.print("state   action\n     ");
		System.out.println();
		for (int i = 0; i < terminalCount; i++)//打印所有终结符
			System.out.print("\t" + terminal.get(i));
		System.out.print("\t#\n");//加入结束符号
		for (int i = 0; i < stateCount; i++) {
			System.out.print(i + "\t");
			for (int j = 0; j < terminalCount + 1; j++) {
				String temp;
				if (j != terminalCount)//正常非终结符
					temp = terminal.get(j);
				else//最后
					temp = "#";
				
				int flag = -1;
				for (Map<String, Object> map : analyseTableAction) {
					if (map.get("state").equals(i)&& map.get("terminal").equals(temp)) {
						ArrayList<String> al = (ArrayList<String>) map.get("value");
						for (int k = 0; k < al.size(); k++) {
							if (k == 0)
								System.out.print(" " + al.get(k));
							if (k > 0)//有冲突的情况
								System.out.print("," + al.get(k));
							if (k == al.size() - 1)
								System.out.print("  ");
						}
						flag = 1;
					}
				}
				if (flag == -1)//没有这一项
					System.out.print("\t");
			}
			System.out.println();
		}

		System.out.println();
		System.out.print("----------------GoTo表---------------\n");
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
				if (flag == -1)//没有这一项
					System.out.print(" \t");
			}
			System.out.println();
		}
		System.out.println();
		System.out.print("----------------分析过程：---------------\n");
		System.out.print("步骤----状态栈--------符号栈----------输入串--------动作-\n");
		System.out.println();
	}

	public void printline(int i, String s_in, String kind, Map<String,String> prodc){//输出分析过程的每一步
		System.out.print(i+"\t");//打印每步序号
		Stack<String> tmp_st = new Stack<String>();
		Stack<Integer> tmp_stk = new Stack<Integer>();

		String temp_str = null;
		int temp_int = 0;
		while(!st_state.empty()){//输出栈中所有内容
			temp_int = st_state.pop();
			System.out.print(temp_int+" ");
			tmp_stk.push(temp_int);//暂时存放
		}
		System.out.print("\t");

		while(!tmp_stk.empty()){
			temp_int = tmp_stk.pop();
			st_state.push(temp_int);//恢复栈
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
			System.out.print("移入\n");
		}else if(kind == "r"){
			System.out.print("按");
			System.out.print(prodc.get("left")+" -> "+prodc.get("right"));
			System.out.print("规约\n");
		}else{
			System.out.print("接受\n");
		}
	}

	@SuppressWarnings("unchecked")
	public boolean isShiBie() {//打印时区别每步动作
		boolean shiBie=true;
		this.st_state.push(0);//初始化栈
		this.st_sym.push("#");
		int i=1;//计数
		
		for (String tmp_str : this.string_in) {//遍历输入的
			if(!tmp_str.equals("#")&&!this.terminal.contains(tmp_str)) {
				System.out.println("不存在的终结符"+tmp_str);
				continue;
			}
			
			int tmp_flag=1;//标志当前输入符处理是否完毕
			while(tmp_flag==1) {
				int tmp_state=this.st_state.peek();//获取栈顶状态
				for (Map<String, Object> tmp_map : this.analyseTableAction) {//对应查找Action分析表
					if(tmp_map.get("state").equals(tmp_state) && tmp_map.get("terminal").equals(tmp_str)) {
						ArrayList<String> tmp_al = (ArrayList<String>) tmp_map.get("value");//取出分析表中填的内容
						
						if(tmp_al==null) {//出现error
							System.out.println("程序不被识别");
							shiBie=false;
							return shiBie;
						} else {//可以识别
							String firstChar=tmp_al.get(0).substring(0, 1);//得到第一个字母
							if(tmp_al.get(0).equals("acc")){//识别成功
								this.st_state.pop();
								this.st_sym.pop();
								this.printline(i,tmp_str,"acc",null);
								i++;
								return shiBie;//成功
							}
							
							if(firstChar.equals("S")) {//移进
								int nextState=Integer.parseInt(tmp_al.get(0).substring(1));//得到下一个状态
								this.st_state.push(nextState);//入栈
								this.st_sym.push(tmp_str);
								tmp_flag=0;//可以退出当前这个输入符
								this.printline(i,tmp_str,"S",null);
								i++;
								break;
							} else if(firstChar.equals("r")) {//规约
								int num=Integer.parseInt(tmp_al.get(0).substring(1));
								Map<String, String> tmp_pro=this.produce.get(num-1);//得到采用哪个产生式规约
								String tmp_right=tmp_pro.get("right");
								String[] temp_str;
								temp_str=tmp_right.split(" ");//拆分目标产生式
								int count=temp_str.length;//个数
								if(tmp_right==""){//空产生式
									count=0;
								}
								while(count!=0){//未规约完
									this.st_state.pop();
									this.st_sym.pop();
									count--;
								}
								this.st_sym.push(tmp_pro.get("left"));//产生式左边压栈
								int tmp_stat=this.st_state.peek();//此时符号栈顶一定是非终结符
								
								//需要goto表相应的压入状态栈
								for(Map<String,Object> tmp_goto : this.analyseTableGoto){//遍历goto表
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
		this.projectUnions.clear();//清空
		this.DFA.clear();
		this.createLR1DFA(null, null);//初始时状态中没有到下一个状态的产生式，且不存在前一状态
		this.createLR1AnalyseTable();
		if (!isLR1()) {//未成功创建起来，即存在冲突
			System.out.println("不属于LR1文法!");
			return;
		}
		this.printProjectsUnions();//项目集族
		this.printTable();
		if(this.isShiBie()){
			System.out.println("成功识别该程序");
		}else{
			System.out.println("文法不能识别该程序");
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
