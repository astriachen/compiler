package syntax;

public class One {
	public static void main(String arg[]){
		String s=".E -";
		int pointPos = s.indexOf(".");//找到.的位置,如s'->.s ，返回值为0
		int spacePos = s.indexOf(" ", pointPos);//求first集的位置，如s'->.s ，返回值为-1
		String nextStr = s.substring(pointPos +1,spacePos);//如s'->s.
		String searchStr = s.substring(spacePos + 1);
		System.out.println(pointPos);
		System.out.println(spacePos);
		System.out.println(nextStr);
		System.out.println(searchStr);
		
		String nowstring = null;//一个一个处理
		String nextstring = null;
		int spos = -1;
		spos = searchStr.indexOf(" ");
		if (spos == -1){//处理其他的
			nowstring = searchStr.substring(0);
			nextstring = "";
		}else{
			nowstring = searchStr.substring(0, spos);
			nextstring = searchStr.substring(spos + 1);
		}
		System.out.println(spos);
		System.out.println(nowstring);
		System.out.println(nextstring);
	}

}
