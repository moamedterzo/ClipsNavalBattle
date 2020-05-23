import javax.swing.*;
import java.awt.*;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Scanner;

public class BattleMap {
    static int rows = 10;
    static int cols = 10;
    JFrame frame = new JFrame();
    JButton[][] grid = new JButton[rows][cols];

    ImageIcon water = new ImageIcon("water.png");
    public static void main(String[] var0) {
        ArrayList<Integer> score=new ArrayList<Integer>();
        BattleMap battleMap = new BattleMap();
        GridLayout gridLayout = new GridLayout(rows, cols);
        battleMap.frame.setLayout(gridLayout);
        int i, j;
        for (i = 0; i < rows; i++) {
            for (j = 0; j < cols; j++) {
                battleMap.grid[i][j] = new JButton();
                battleMap.grid[i][j].setIcon(null);
            }
        }
        ArrayList<String> output = battleMap.readOutput();
        for (i = 0; i < output.size(); i++) {
            String[] line = output.get(i).split("\\s+");
            if (output.get(i).contains("(k-cell")) {
                char x = ' ', y = ' ';
                for (j = 0; j < line.length; j++) {
                    switch (line[j]) {
                        case "(x":
                            x = line[j + 1].charAt(0);
                            break;
                        case "(y":
                            y = line[j + 1].charAt(0);
                            break;
                        case "(content":
                            String content = line[j + 1];
                            content = content.replace(")", "");
                            content += ".png";
                            if (battleMap.grid[Integer.parseInt(String.valueOf(x))][Integer.parseInt(String.valueOf(y))].getIcon() == null)
                                battleMap.grid[Integer.parseInt(String.valueOf(x))][Integer.parseInt(String.valueOf(y))].setIcon(new ImageIcon(content));
                            break;
                    }
                }

            } else if (output.get(i).contains("(action fire)")) {
                char x = ' ', y = ' ';
                for (j = 0; j < line.length; j++) {
                    switch (line[j]) {
                        case "(x":
                            x = line[j + 1].charAt(0);
                            break;
                        case "(y":
                            y = line[j + 1].charAt(0);
                            battleMap.grid[Integer.parseInt(String.valueOf(x))][Integer.parseInt(String.valueOf(y))].setIcon(new ImageIcon("hit-boat.png"));
                            break;
                    }
                }

            } else if (output.get(i).contains("(cell")) {
                String contento = "";
                char x = ' ', y = ' ';
                for (j = 0; j < line.length; j++) {
                    switch (line[j]) {
                        case "(x":
                            x = line[j + 1].charAt(0);
                            break;
                        case "(y":
                            y = line[j + 1].charAt(0);
                            break;
                        case "(content":
                            contento = line[j + 1];
                            contento = contento.replace(")", "");
                            contento += ".png";
                        case "(status":
                            String content = line[j + 1];
                            content = content.replace(")", "");
                            content += ".png";
                            if (contento.equalsIgnoreCase("boat.png")) {
                                battleMap.grid[Integer.parseInt(String.valueOf(x))][Integer.parseInt(String.valueOf(y))].setIcon(new ImageIcon("middle.png"));
                            } else if ((content.equalsIgnoreCase("missed.png") || content.equalsIgnoreCase("guessed.png"))) {
                                battleMap.grid[Integer.parseInt(String.valueOf(x))][Integer.parseInt(String.valueOf(y))].setIcon(new ImageIcon(content));
                            } else if (content.equalsIgnoreCase("none.png")) {
                                battleMap.grid[Integer.parseInt(String.valueOf(x))][Integer.parseInt(String.valueOf(y))].setIcon(new ImageIcon("water.png"));
                            }
                            break;
                    }
                }
            }else if(output.get(i).contains("(statistics")){
                for (j = 0; j < line.length; j++) {
                    try{
                        int num = Integer.parseInt(line[j].replace(")", ""));
                        score.add(num);
                    } catch (NumberFormatException e) {
                    }
                }
            }
        }
        for (i = 0; i < rows; i++) {
            for (j = 0; j < cols; j++) {
                battleMap.frame.add(battleMap.grid[i][j]);
            }
        }
        battleMap.frame.setVisible(true);
        battleMap.frame.setSize(800, 600);
        battleMap.frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        JOptionPane.showMessageDialog(null,"Num fire ok: "+score.get(0)+"\nNum fire ko: "+score.get(1)+"\nNum guess ok: "+score.get(2)+"\nNum guess ko: "+score.get(3)+"\nNum safe: "+score.get(4)+"\nNum sink: "+score.get(5),"Punteggio totalizzato",JOptionPane.INFORMATION_MESSAGE);
    }

    public ArrayList<String> readOutput() {
        ArrayList<String> output = new ArrayList<String>();
        try {
            File myObj = new File("output2.txt");
            Scanner myReader = new Scanner(myObj);
            while (myReader.hasNextLine()) {
                String data = myReader.nextLine();
                output.add(data);
            }
            myReader.close();
        } catch (FileNotFoundException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }
        return output;
    }
}